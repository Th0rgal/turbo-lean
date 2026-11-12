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

open Lean Elab

namespace TurboLean.ZygoteWorker

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

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

def hydrateRecAuditEnv (env0 : Environment) : IO Environment := do
  if Lean.classExtension.getState env0 |>.outParamMap.contains ``Monad then
    return env0
  let mut e := env0
  e ← hydrateOnePersistentExt Lean.classExtension e
  e ← hydrateOnePersistentExt Lean.Meta.instanceExtension.ext e
  e ← hydrateOnePersistentExt Lean.Meta.defaultInstanceExtension e
  e ← hydrateOnePersistentExt Lean.reducibilityExtraExt.ext e
  e ← hydrateOnePersistentExt Lean.Meta.Match.Extension.extension e
  e ← hydrateOnePersistentExt Lean.Elab.WF.wfPreprocessSimpExtension.ext e
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

/-- 256-bit cryptographic BLAKE3 content digest over raw artifact bytes. -/
def hashBytesBlake3Hex (bs : ByteArray) : String :=
  TurboLean.Blake3.blake3Bytes bs

/-- Canonical BLAKE3 digest of `(c.levelParams, c.type)` under the `statement-v1` schema,
    normalizing module-local private constant names so probe, shard, and module elaborations match. -/
def kernelStatementHash (c : ConstantInfo) (localMod? : Option Name := none) : String :=
  let j := TurboLean.StatementHash.statement c (TurboLean.StatementHash.normalizeLocalPrivateName localMod?)
  TurboLean.Blake3.blake3Bytes j.compress.toUTF8

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

def hydrateCompilerAuditEnv (env0 : Environment) : IO Environment := do
  let mut e := env0
  e ← hydrateOnePersistentExt Lean.Compiler.CSimp.ext.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.inlineAttrs.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.nospecializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.weakSpecializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.specializeAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.implementedByAttr.ext e
  e ← hydrateOnePersistentExt Lean.Compiler.LCNF.specExtension e
  e ← hydrateOnePersistentExt Lean.Compiler.LCNF.Simp.ConstantFold.folderExt e
  e ← hydrateOnePersistentExt Lean.Compiler.LCNF.passManagerExt e
  e ← hydrateOnePersistentExt Lean.Meta.Match.Extension.extension e
  e ← hydrateOnePersistentExt Lean.classExtension e
  e ← hydrateOnePersistentExt Lean.Meta.instanceExtension.ext e
  return e

def runPureLcnfPass : Lean.Compiler.LCNF.Pass → Array (Lean.Compiler.LCNF.Decl .pure) →
    Lean.Compiler.LCNF.CompilerM (Array (Lean.Compiler.LCNF.Decl .pure))
  | { phase := .base, phaseOut := .base, run, .. }, cur =>
    Lean.Compiler.LCNF.withPhase .base (run cur)
  | _, cur => pure cur

def compileSingleBaseLcnfDecl (env : Environment) (declName : Name) :
    IO (Option (Lean.Compiler.LCNF.Decl .pure)) := do
  let action : Lean.Compiler.LCNF.CompilerM (Option (Lean.Compiler.LCNF.Decl .pure)) :=
    Lean.withAtLeastMaxRecDepth 8192 do
      let initDecl ← Lean.Compiler.LCNF.toDecl declName
      let mut cur := Lean.Compiler.LCNF.markRecDecls #[initDecl]
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
      (Lean.Compiler.LCNF.CompilerM.run (Lean.withAtLeastMaxRecDepth 8192 (Lean.Compiler.LCNF.toDecl declName)))
      { fileName := "<csimp-audit>", fileMap := default, maxHeartbeats := 0 } { env }
    return some d
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
        (Lean.getExternNameFor env `c cinfo.name).any fun sym => ffiAllow.contains (m, cinfo.name, sym)
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
    (allowSorry : Bool := false) (isImportAudit : Bool := false) : IO (List String × List String) := do
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
        (acc ++ [s!"[TurboLean.KernelGate] local csimp replacement `{thmName}` ({lhs} <-> {rhs}) rewrote compiled code of `{callerName}` in `{modLabel}`{kernelPolicyHint "csimp" thmName}"],
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
      if !storedBaseMap.contains callerName || (env.find? callerName).isNone then
        let compiledConsts := collectCompiledCodeConsts env callerName
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
        | none =>
          for (thmName, lhs, rhs) in localCands do
            if ownerName != lhs && ownerName != rhs then
              let (o, s) := emitHit thmName lhs rhs callerName out seenLocalHit
              out := o; seenLocalHit := s
        | some tdBase =>
          let mut activeCands : Array (Name × Name × Name) := #[]
          for (thmName, lhs, rhs) in localCands do
            if !seenLocalHit.contains (thmName, callerName) && ownerName != lhs && ownerName != rhs then
              let envCand := Lean.Compiler.CSimp.ext.addEntry envMod
                { fromDeclName := lhs, toDeclName := rhs, thmName := thmName }
              let changed := match ← compileSingleToLcnfDecl envCand callerName with
                | none => true
                | some tdCand => !lcnfDeclAlphaEqv tdBase tdCand
              if changed then
                activeCands := activeCands.push (thmName, lhs, rhs)
          if !activeCands.isEmpty then
            let baseMatchesStored := match ← compileSingleBaseLcnfDecl envMod callerName with
              | some rd => lcnfDeclAlphaEqvModuloSpec bStored rd
              | none => false
            if !baseMatchesStored then
              for (thmName, lhs, rhs) in activeCands do
                let (o, s) := emitHit thmName lhs rhs callerName out seenLocalHit
                out := o; seenLocalHit := s
    if mdata.isModule && storedBaseMap.isEmpty then
      for callerInfo in mdata.constants do
        let callerName := callerInfo.name
        if !(callerInfo matches .thmInfo _ | .axiomInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _) &&
           !Lean.Compiler.hasMacroInlineAttribute envMod callerName then
          match ← compileSingleToLcnfDecl envMod callerName with
          | none =>
            for (thmName, lhs, rhs) in localCands do
              if callerName != lhs && callerName != rhs then
                let (o, s) := emitHit thmName lhs rhs callerName out seenLocalHit
                out := o; seenLocalHit := s
          | some tdBase =>
            for (thmName, lhs, rhs) in localCands do
              if !seenLocalHit.contains (thmName, callerName) && callerName != lhs && callerName != rhs then
                let envCand := Lean.Compiler.CSimp.ext.addEntry envMod
                  { fromDeclName := lhs, toDeclName := rhs, thmName := thmName }
                let changed := match ← compileSingleToLcnfDecl envCand callerName with
                  | none => true
                  | some tdCand => !lcnfDeclAlphaEqv tdBase tdCand
                if changed then
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
  for (ownerModIdx?, entry) in allCSimpEntries do
    let key := (entry.thmName, entry.fromDeclName, entry.toDeclName)
    if !seenCSimp.contains key && (isImportAudit || ownerModIdx?.any targetIdxs.contains || entryTouchesTarget entry) then
      seenCSimp := seenCSimp.insert key
      violations := violations ++ (← checkCSimpEntry entry ownerModIdx?)
  return (violations, sorryDecls)

/-- Audit a single compiled shard module: like `auditModuleSlice`, but exempts validated prefix
    stubs named in `stubOk` and also returns the module's non-stub theorems (plus their canonical
    `statement-v1` kernel type hashes), read from the kernel environment (never from elaboration
    output) so the host can confirm every audited target was actually declared with the expected
    kernel type. -/
def auditShardModule (target : String × Name) (ffiAllow : Array (Name × Name × String))
    (stubOk : Array String) (fastMap : List (String × String) := [])
    (allowSorry : Bool := false) :
    IO (List String × Array String × List (String × String) × List String) := do
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
    let (impViolations, impSorryDecls) ← auditImportedModulesInEnv env #[target] ffiAllow patterns csimpPatterns stubs unsafePatterns implByPatterns false allowSorry
    return (stubViolations ++ fastViolations ++ impViolations, decls, declTypes, impSorryDecls)
  catch e =>
    return ([s!"[TurboLean.KernelGate] failed to import `{target.1}` for audit: {e}"], #[], [], [])

def auditModuleSlice (slice : Array (String × Name)) (ffiAllow : Array (Name × Name × String) := #[])
    (skipChildReplay : Bool := false) (allowSorry : Bool := false)
    (isImportAudit : Bool := false) : IO (List String) := do
  if slice.isEmpty then
    return []
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
    let (vs, _) ← auditImportedModulesInEnv env slice ffiAllow patterns csimpPatterns {} unsafePatterns implByPatterns skipChildReplay allowSorry isImportAudit
    return vs
  | .error errMsg =>
    if slice.size == 1 then
      let (rawStr, _) := slice[0]!
      return [s!"[TurboLean.KernelGate] failed to import `{rawStr}` for audit: {errMsg}"]
    -- Compacted `.olean` import regions are never unmapped within a single OS process; bisecting
    -- `Lean.importModules` in-process would accumulate mappings across retries and exhaust the
    -- untrusted 8 GiB `RLIMIT_DATA` cap. Spawn fresh OS child processes for each half instead.
    let app := (← IO.appPath).toString
    let ffiFlags : Array String := ffiAllow.map fun (m, d, sym) =>
      s!"--ffi-allow={m}={d}={sym}"
    let replayFlags : Array String := if skipChildReplay then #["--skip-child-replay"] else #[]
    let sorryFlags : Array String := if allowSorry then #["--allow-sorry"] else #[]
    let importFlags : Array String := if isImportAudit then #["--audit-imports"] else #[]
    let runSubSlice (sub : Array (String × Name)) : IO (List String) := do
      let modFlags := sub.map (·.1)
      let child ← IO.Process.output {
        cmd := app
        args := #["--audit-modules"] ++ importFlags ++ replayFlags ++ sorryFlags ++ ffiFlags ++ modFlags
      }
      if child.exitCode == 0 then
        return []
      let lastJson? := (child.stdout.splitOn "\n").reverse.find? fun l =>
        let t := l.trimAscii.toString
        t.startsWith "{" && t.endsWith "}"
      let detail := (lastJson?.getD child.stdout).trimAscii.toString
      let errTail := child.stderr.trimAscii.toString
      let summary := if detail.isEmpty then errTail else if errTail.isEmpty then detail else s!"{detail} ({errTail})"
      return [s!"[TurboLean.KernelGate] sub-batch audit failed (exit {child.exitCode}) on {modFlags.toList}: {summary}"]
    let mid := slice.size / 2
    let v1 ← runSubSlice (slice.extract 0 mid)
    let v2 ← runSubSlice (slice.extract mid slice.size)
    return v1 ++ v2

def auditCompiledModules (modNames : List String) (ffiAllow : Array (Name × Name × String) := #[])
    (skipChildReplay : Bool := false) (allowSorry : Bool := false)
    (isImportAudit : Bool := false) : IO (Bool × List String) := do
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
    return (initViolations.isEmpty, initViolations)
  let sliceViolations ← auditModuleSlice parsed ffiAllow skipChildReplay allowSorry isImportAudit
  let allViolations := initViolations ++ sliceViolations
  return (allViolations.isEmpty, allViolations)

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

structure TimeoutHotspotEntry where
  kind : String
  label : String
  line : Nat
  elapsedMs : Nat
  heartbeats : Nat

structure SimpHotspotEntry where
  lemmaName : String
  attempts : Nat
  succeeded : Nat

private partial def walkHotspotMessageData
    (md : MessageData)
    (cmdLine : Nat)
    (traceOut : IO.Ref (Array TimeoutHotspotEntry))
    (simpOut : IO.Ref (Std.HashMap String (Nat × Nat)))
    (visitedNodes : IO.Ref Nat) : IO Unit := do
  let n ← visitedNodes.get
  if n >= 8192 then
    return
  visitedNodes.set (n + 1)
  match md with
  | .trace data hdr children =>
    let clsStr := data.cls.toString
    if clsStr.startsWith "Meta.Tactic.simp." then
      let hdrTxt ← (hdr.toString : IO String)
      let firstLine := ((hdrTxt.splitOn "\n").headD hdrTxt).trimAscii.toString
      let rawLemma := ((firstLine.splitOn ":").headD firstLine).trimAscii.toString
      let cleanLemma := if rawLemma.startsWith "[" then
          match rawLemma.splitOn "]" with
          | _ :: rest => (String.intercalate "]" rest).trimAscii.toString
          | [] => rawLemma
        else rawLemma
      if !cleanLemma.isEmpty && !cleanLemma.startsWith "==" && cleanLemma.length <= 160 then
        let isRewrite := clsStr == "Meta.Tactic.simp.rewrite"
        let isSuccess := isRewrite || (match data.result? with | some .success => true | _ => false)
        let curMap ← simpOut.get
        let (att, succ) := curMap[cleanLemma]?.getD (0, 0)
        simpOut.set (curMap.insert cleanLemma (att + 1, succ + (if isSuccess then 1 else 0)))
    if data.stopTime > data.startTime then
      let durSec := data.stopTime - data.startTime
      let durMsFloat := durSec * 1000.0
      let durMs := durMsFloat.toUInt64.toNat
      if durMs >= 1 && (clsStr.startsWith "Elab." || clsStr == "Kernel" || clsStr.startsWith "Meta.Tactic") then
        let hdrTxt ← (hdr.toString : IO String)
        let firstLine := ((hdrTxt.splitOn "\n").headD hdrTxt).trimAscii.toString
        let clipped := if firstLine.length > 120 then (firstLine.take 120).toString else firstLine
        let label := if clipped.isEmpty then clsStr else s!"[{clsStr}] {clipped}"
        let arr ← traceOut.get
        if arr.size < 256 then
          traceOut.set (arr.push { kind := "trace", label := label, line := cmdLine, elapsedMs := durMs, heartbeats := 0 })
    for child in children do
      walkHotspotMessageData child cmdLine traceOut simpOut visitedNodes
  | .withContext _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .withNamingContext _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .nest _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .group inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .compose a b =>
    walkHotspotMessageData a cmdLine traceOut simpOut visitedNodes
    walkHotspotMessageData b cmdLine traceOut simpOut visitedNodes
  | .tagged _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .ofWidget _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .ofLazy fn _ =>
    let dyn ← (fn none : BaseIO Dynamic)
    if let some inner := dyn.get? MessageData then
      walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | other =>
    if let some inner := originatingMessage? other then
      walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes

/-- Bounded command-by-command diagnostic pass executed ONLY after a timeout or heartbeat/recursion
    exhaustion failure. Enables `profiler` + `trace.Meta.Tactic.simp.*` on an isolated state, records
    per-command wall-clock / heartbeat consumption and `simp` lemma rewrite/unify counts, and formats
    additive `,"timeout_hotspots":[...],"simp_hotspots":[...]` JSON fields (never `ok: true`). -/
def diagnoseShardHotspots
    (baseEnv : Environment)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (encodedLeanArgs : String := "") : IO (Nat × Nat × List String × List String × String) := do
  let initOpts ← applyEncodedLeanArgs {} encodedLeanArgs
  let profOpts0 := initOpts.setBool `profiler true
  let profOpts1 := profOpts0.set `profiler.threshold (1 : Nat)
  let profOpts2 := profOpts1.setBool `trace.Meta.Tactic.simp.rewrite true
  let profOpts3 := profOpts2.setBool `trace.Meta.Tactic.simp.unify true
  let profOpts := profOpts3.setBool `trace.Meta.Tactic.simp.discharge true
  let curHb := profOpts.get `maxHeartbeats (200000 : Nat)
  let diagHb := if curHb == 0 || curHb > 250000 then 250000 else curHb
  let opts ← withToolchainSatSolver (profOpts.set `maxHeartbeats diagHb)
  let ictx := Parser.mkInputContext code fileName
  let initState := Command.mkState baseEnv {} opts
  let mut fstate : Frontend.State := {
    commandState := initState
    parserState := {}
    cmdPos := 0
  }
  let cmdHotspotsRef ← IO.mkRef (#[] : Array TimeoutHotspotEntry)
  let traceHotspotsRef ← IO.mkRef (#[] : Array TimeoutHotspotEntry)
  let simpMapRef ← IO.mkRef ({} : Std.HashMap String (Nat × Nat))
  let visitedRef ← IO.mkRef (0 : Nat)
  let mut allMsgs : List String := []
  let mut allErrs : List String := []
  let mut prevMsgCount : Nat := 0
  let tStart ← IO.monoNanosNow
  let hbStart ← IO.getNumHeartbeats
  let mut done := false
  let mut stepCount : Nat := 0
  while !done && stepCount < 512 do
    stepCount := stepCount + 1
    let cmdPosBefore := fstate.parserState.pos
    let cmdLine := (ictx.fileMap.toPosition cmdPosBefore).line
    let cT0 ← IO.monoNanosNow
    let cHb0 ← IO.getNumHeartbeats
    let (_, (_, fstate')) ← IO.FS.withIsolatedStreams ((Frontend.processCommand.run { inputCtx := ictx }).run fstate) (isolateStderr := false)
    let cT1 ← IO.monoNanosNow
    let cHb1 ← IO.getNumHeartbeats
    let cmdMs := (cT1 - cT0) / 1000000
    let cmdHbs := cHb1 - cHb0
    let cmdStx? := fstate'.commands.back?
    let isTerm := cmdStx?.any Parser.isTerminalCommand
    if !isTerm then
      let kindStr := match cmdStx? with | some stx => stx.getKind.toString | none => "command"
      let rawSlice := (String.Pos.Raw.extract code cmdPosBefore fstate'.parserState.pos).trimAscii.toString
      let firstLine := ((rawSlice.splitOn "\n").headD rawSlice).trimAscii.toString
      let snippet := if firstLine.length > 100 then (firstLine.take 100).toString else firstLine
      let label := if snippet.isEmpty then kindStr else snippet
      let curCmds ← cmdHotspotsRef.get
      cmdHotspotsRef.set (curCmds.push {
        kind := "command"
        label := label
        line := cmdLine
        elapsedMs := cmdMs
        heartbeats := cmdHbs
      })
    let msgList := fstate'.commandState.messages.toList
    let newMsgs := msgList.drop prevMsgCount
    prevMsgCount := msgList.length
    for msg in newMsgs do
      walkHotspotMessageData msg.data msg.pos.line traceHotspotsRef simpMapRef visitedRef
      let txt ← msg.data.toString
      let sevStr := match msg.severity with
        | .error => "error"
        | .warning => "warning"
        | .information => "info"
      let formatted := s!"{msg.fileName}:{msg.pos.line}:{msg.pos.column}: {sevStr}: {txt.trimAsciiEnd.toString}"
      allMsgs := allMsgs ++ [formatted]
      if msg.severity == .error then
        allErrs := allErrs ++ [formatted]
    for td in fstate'.commandState.traceState.traces do
      walkHotspotMessageData td.msg cmdLine traceHotspotsRef simpMapRef visitedRef
    fstate := fstate'
    let nowNs ← IO.monoNanosNow
    if isTerm || ((nowNs - tStart) / 1000000) >= 3500 then
      done := true
  if allMsgs.any isRuntimePanicText then
    allErrs := allErrs ++ [runtimePanicErr]
  if allErrs.isEmpty then
    allErrs := ["[TurboLean.Diagnostics] diagnostic hotspot pass completed"]
  let cmdArr ← cmdHotspotsRef.get
  let traceArr ← traceHotspotsRef.get
  let combined := (cmdArr ++ traceArr).qsort fun a b =>
    if a.heartbeats != b.heartbeats then a.heartbeats > b.heartbeats
    else a.elapsedMs > b.elapsedMs
  let topTimeout := combined.extract 0 (Nat.min 8 combined.size)
  let simpMap ← simpMapRef.get
  let simpArr := (simpMap.toArray.map fun (k, (att, succ)) =>
    ({ lemmaName := k, attempts := att, succeeded := succ } : SimpHotspotEntry)).qsort fun a b =>
      if a.attempts != b.attempts then a.attempts > b.attempts
      else a.succeeded > b.succeeded
  let topSimp := simpArr.extract 0 (Nat.min 8 simpArr.size)
  let timeoutJsonItems := topTimeout.toList.map fun e =>
    s!"\{\"kind\":\"{jsonEscape e.kind}\",\"label\":\"{jsonEscape e.label}\",\"line\":{e.line},\"elapsed_ms\":{e.elapsedMs},\"heartbeats\":{e.heartbeats}}"
  let simpJsonItems := topSimp.toList.map fun e =>
    s!"\{\"lemma\":\"{jsonEscape e.lemmaName}\",\"attempts\":{e.attempts},\"succeeded\":{e.succeeded}}"
  let suffix := s!",\"timeout_hotspots\":[{String.intercalate "," timeoutJsonItems}],\"simp_hotspots\":[{String.intercalate "," simpJsonItems}]"
  let tEnd ← IO.monoNanosNow
  let hbEnd ← IO.getNumHeartbeats
  return ((tEnd - tStart) / 1000, hbEnd - hbStart, allMsgs, allErrs, suffix)

end TurboLean.ZygoteWorker

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
    let (ok, violations, decls, declTypes, sorryDecls) ← match shardFlag.isEmpty, audited, fastMapOpt with
      | true, _, _ =>
        if stubArgs.isEmpty && fastMapArgs.isEmpty then
          let (ok, vs) ← TurboLean.ZygoteWorker.auditCompiledModules mods ffiAllow (!skipReplayFlags.isEmpty) allowSorry isImportAudit
          pure (ok, vs, none, none, [])
        else pure (false, ["[TurboLean.KernelGate] --stub-ok / --fast-map requires --shard"], none, none, [])
      | false, _, none =>
        pure (false, ["[TurboLean.KernelGate] malformed --fast-map argument"], none, none, [])
      | false, [m], some fmap =>
        if !skipReplayFlags.isEmpty then
          pure (false, ["[TurboLean.KernelGate] --skip-child-replay forbidden with --shard"], none, none, [])
        else
          let nm := TurboLean.ZygoteWorker.parseModuleName m.trimAscii.toString
          let (vs, ds, dts, sds) ← TurboLean.ZygoteWorker.auditShardModule (m.trimAscii.toString, nm) ffiAllow
            (stubArgs.toArray.map fun a => (a.drop 10).toString) fmap allowSorry
          pure (vs.isEmpty && !nm.isAnonymous, vs, some ds, some dts, sds)
      | false, _, _ => pure (false, ["[TurboLean.KernelGate] --shard audits exactly one module"], none, none, [])
    let ok := ok && ffiAllow.size == ffiArgs.length
    let declsJson := match decls with
      | some ds => s!",\"decls\":[{TurboLean.ZygoteWorker.jsonStrList ds.toList}]"
      | none => ""
    let declTypesJson := match declTypes with
      | some dts => s!",\"decl_types\":\{{TurboLean.ZygoteWorker.jsonKvObj dts}}"
      | none => ""
    let sorryJson := if sorryDecls.isEmpty then ""
      else s!",\"used_sorry\":true,\"sorry_decls\":[{TurboLean.ZygoteWorker.jsonStrList sorryDecls}]"
    stdout.putStrLn s!"\{\"ok\":{ok},\"audited\":[{TurboLean.ZygoteWorker.jsonStrList audited}],\"violations\":[{TurboLean.ZygoteWorker.jsonStrList violations}]{declsJson}{declTypesJson}{sorryJson}}"
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
