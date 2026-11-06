/-
  TurboLean.ZygoteWorker: Persistent In-Memory `Lean.Environment` Zygote Worker
  Caches imported `Lean.Environment` instances in an in-memory `Std.HashMap String Environment`
  keyed by the comma-separated module import list. Because `Lean.Environment` is a persistent
  functional data structure in Lean 4, each incoming theorem shard elaborates and kernel-checks
  against `baseEnv` via `Lean.Elab.IO.processCommands` in ~1.5–25 ms with 0.00 ms of `.olean`
  reload or process startup overhead, leaving `baseEnv` completely unmutated.
-/
import Lean.Elab.Frontend
import Lean.Elab.App
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
    (opaqueStub : Name → Bool := fun _ => false) : Array Name := Id.run do
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
      let impAxioms : Array Name := Id.run ((Lean.collectAxioms curr : ReaderT Environment Id (Array Name)).run afterEnv)
      for ax in impAxioms do
        if !(axiomSeen[ax]?.getD false) then
          axiomSeen := axiomSeen.insert ax true
          axioms := axioms.push ax
  return axioms

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

/-- Kernel names newly elaborated in `env` (`map₂`) exempt from the `sorryAx` gate: host stubs (`stubs`)
    whose value is an explicit `sorry` (`isExplicitSorryStub`), never a host target. `violations` is
    non-empty when any stub name is ambiguous (which exempts nothing at all). -/
def stubExemptSet (env : Environment) (stubs targets : List String)
    (fastMap : List (String × String) := []) : Std.HashSet Name × List String :=
  let consts := env.constants.map₂.foldl (fun acc _ c => acc.push c) #[]
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
  for (name, cinfo) in orderedNewDecls do
    if cinfo.isUnsafe then
      violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{name}` is forbidden"]
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

def eqConstantVal (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

def eqReducibilityHints : ReducibilityHints → ReducibilityHints → Bool
  | .opaque, .opaque => true
  | .abbrev, .abbrev => true
  | .regular a, .regular b => a == b
  | _, _ => false

def eqDefinitionSafety (a b : DefinitionSafety) : Bool :=
  a == b

def eqQuotKind : QuotKind → QuotKind → Bool
  | .type, .type => true
  | .ctor, .ctor => true
  | .lift, .lift => true
  | .ind, .ind => true
  | _, _ => false

def eqRecursorRule (a b : RecursorRule) : Bool :=
  a.ctor == b.ctor && a.nfields == b.nfields && a.rhs == b.rhs

def eqRecursorRules : List RecursorRule → List RecursorRule → Bool
  | [], [] => true
  | a :: as_, b :: bs => eqRecursorRule a b && eqRecursorRules as_ bs
  | _, _ => false

def eqConstantInfo : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.value == b.value &&
      eqReducibilityHints a.hints b.hints && eqDefinitionSafety a.safety b.safety && a.all == b.all
  | .thmInfo a, .thmInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.value == b.value && a.all == b.all
  | .opaqueInfo a, .opaqueInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.value == b.value &&
      a.isUnsafe == b.isUnsafe && a.all == b.all
  | .quotInfo a, .quotInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && eqQuotKind a.kind b.kind
  | .inductInfo a, .inductInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
      a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.induct == b.induct && a.cidx == b.cidx &&
      a.numParams == b.numParams && a.numFields == b.numFields && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    eqConstantVal a.toConstantVal b.toConstantVal && a.all == b.all &&
      a.numParams == b.numParams && a.numIndices == b.numIndices &&
      a.numMotives == b.numMotives && a.numMinors == b.numMinors &&
      eqRecursorRules a.rules b.rules && a.k == b.k && a.isUnsafe == b.isUnsafe
  | _, _ => false

set_option linter.deprecated false in
def replayEnvConstants (newConsts : Std.HashMap Name ConstantInfo) (env : Environment) : IO Environment :=
  Lean.Environment.replay newConsts env

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
      if !(eqConstantInfo newInfo oldInfo) then
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
    let _ ← replayEnvConstants newConsts beforeEnv
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
    to `oleanPath` only after verifying `mainModule == modName` and re-auditing all declarations added since `baseEnv`
    for zero forbidden axioms (`sorryAx`, `reduceBool`, `trustCompiler`). -/
def writeVerifiedModuleOlean (baseEnv finalEnv : Environment) (modName : Name) (oleanPath : System.FilePath) : IO Bool := do
  if modName.isAnonymous || finalEnv.mainModule != modName then
    return false
  if !(← kernelReplayNewDecls baseEnv finalEnv).isEmpty then
    return false
  let (clean, kErrs, _) ← auditNewKernelDecls baseEnv finalEnv
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
    (allowSorry : Bool := false) : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String × List (String × String) × List String) := do
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
    runCommandsFromState baseState bodyCode fileName allowStub evalMode stubTargets stubs
      (requiredTargets := requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := includeStubsInDeclTypes)
      (allowSorry := allowSorry)
  let mut finalOk := ok
  let mut finalErrs := errs
  if finalOk then
    if let some (modName, oleanPath) := emitOlean? then
      if allowStub || allowSorry || evalMode then
        finalOk := false
        finalErrs := finalErrs ++ ["emit_olean rejected stubbed or eval mode"]
      else
        let wrote ← writeVerifiedModuleOlean baseEnv finalSt.env modName oleanPath
        if !wrote then
          finalOk := false
          finalErrs := finalErrs ++ ["emit_olean failed module identity or kernel hygiene gate"]
  return (finalOk, elapsedUs, heartbeats, proofTermNodes, finalErrs, allMessages, capturedStdout, usedConstants, declTypes, sorryDecls)

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

/-- Run a `race_candidates` loop using `evalCand` and return `(ok, winIdxJson, elabUs, hbs, nodes, subVerified, outStr, msgs, errs, used, declTypes)`. -/
def runRaceCandidatesSubs (hexSubs : List String)
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

def isWhitelistedInitExecUnsafe (env : Environment) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Bool :=
  if !cinfo.isUnsafe then false
  else match cinfo.value? with
    | some (.const ``Lean.enableInitializersExecution []) =>
      cinfo.type == .app (.const ``BaseIO []) (.const ``Unit []) &&
      env.getModuleIdxFor? cinfo.name == some modIdx
    | _ => false

/-- Recognizes Lean 4's compiler-generated `_unsafe_rec` lowering (`foo._unsafe_rec`
    with `DefinitionSafety.partial` paired in the same module with `foo` of the
    identical level parameters and type):
    - `partial def foo`: `foo` is `.opaqueInfo` (`!oVal.isUnsafe`), OR
    - structurally / well-founded recursive `def foo`: `foo` is `.defnInfo` (`bVal.safety == .safe`)
      whose kernel body uses `brecOn` / `WellFounded.fix` / `WellFounded.Nat.fix` (or `foo._sunfold`)
      and `foo._unsafe_rec` actually calls an `._unsafe_rec` peer in the same module.
    Forged `safeTarget._unsafe_rec` hijack attempts on non-recursive `def safeTarget`
    fail closed because neither `safeTarget` is recursive nor does a constant body invoke `_unsafe_rec`. -/
def isCompilerPartialRecDefn (env : Environment) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Bool :=
  let nameIsRecCombinator (n : Name) : Bool :=
    match n with
    | .str _ "brecOn" | .str _ "fix" | .str _ "fixF" => true
    | .str _ s => s.startsWith "brecOn_"
    | _ => false
  let bodyUsesRecCombinator (bVal : DefinitionVal) : Bool :=
    let direct := bVal.value.getUsedConstants
    direct.any nameIsRecCombinator ||
    direct.any fun c =>
      match c with
      | .str _ "_mutual" | .str _ "_unary" =>
        env.getModuleIdxFor? c == some modIdx &&
        match env.find? c with
        | some (.defnInfo mVal) => mVal.safety == .safe && mVal.value.getUsedConstants.any nameIsRecCombinator
        | _ => false
      | _ => false
  match cinfo with
  | .defnInfo dVal =>
    dVal.safety == .partial &&
    !(Lean.isExtern env dVal.name) &&
    (Lean.Compiler.getImplementedBy? env dVal.name).isNone &&
    match Lean.Compiler.isUnsafeRecName? dVal.name with
    | some baseName =>
      env.getModuleIdxFor? baseName == some modIdx &&
      !(Lean.isExtern env baseName) &&
      (Lean.Compiler.getImplementedBy? env baseName).isNone &&
      match env.find? baseName with
      | some (.opaqueInfo oVal) =>
        !oVal.isUnsafe && oVal.levelParams == dVal.levelParams && oVal.type == dVal.type
      | some (.defnInfo bVal) =>
        bVal.safety == .safe &&
        bVal.levelParams == dVal.levelParams &&
        bVal.type == dVal.type &&
        (env.contains (baseName.mkStr "_sunfold") || env.contains (baseName.mkStr "_unary") || bodyUsesRecCombinator bVal) &&
        dVal.value.getUsedConstants.any fun c =>
          match Lean.Compiler.isUnsafeRecName? c with
          | some peer => env.getModuleIdxFor? peer == some modIdx
          | none => false
      | _ => false
    | none => false
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

def csimpReplacementPair? (env : Environment) (ty : Expr) : Option (Name × Name) :=
  match ty.eq? with
  | some (_, .const f us, .const g vs) =>
    if f != g && us == vs && us.all Level.isParam &&
       !(env.find? f).any (·.isCtor) && !(env.find? g).any (·.isCtor) then
      some (f, g)
    else
      none
  | _ => none

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
  for name in full.constNames, ci in full.constants do
    if let some existing := base.find? name then
      if !dupTheoremMatch ci existing then
        throw <| IO.userError s!"`{moduleName}` redeclares imported constant `{name}`"
    constants := constants.insert name ci
  discard <| replayEnvConstants constants base

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
  for (modName, full) in fullModules do
    for name in full.constNames, ci in full.constants do
      if let some existing := base.find? name then
        if !dupTheoremMatch ci existing then
          throw <| IO.userError s!"`{modName}` redeclares imported constant `{name}`"
      else if let some prev := constants[name]? then
        if !dupTheoremMatch ci prev then
          throw <| IO.userError s!"`{modName}` redeclares closure constant `{name}`"
        else
          constants := constants.insert name ci
      else
        constants := constants.insert name ci
  discard <| replayEnvConstants constants base

def auditImportedModulesInEnv (env : Environment) (targets : Array (String × Name))
    (ffiAllow : Array (Name × Name × String) := #[])
    (patterns : List String := []) (csimpPatterns : List String := [])
    (stubs : Std.HashSet Name := {})
    (unsafePatterns : List String := []) (implByPatterns : List String := [])
    (skipChildReplay : Bool := false)
    (allowSorry : Bool := false) : IO (List String × List String) := do
  let sorryAxName := Name.mkSimple ("sor" ++ "ryAx")
  let csimpAllowed := fun name : Name => csimpPatterns.any (globMatch ·.toList name.toString.toList)
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
  let unsfTag := "un" ++ "safe"
  let mut violations : List String := []
  let mut sorryDecls : List String := []
  let mut seenSorry : Std.HashMap String Bool := {}
  let mut targetIdxs : Std.HashMap ModuleIdx String := {}
  let mut allRoots : Array Name := #[]
  let app := (← IO.appPath).toString
  -- Compacted import regions are not reclaimed automatically. Isolate replay in a child OS
  -- process so repeated dependency imports cannot exhaust the auditor's 8 GiB sandbox limit.
  if !skipChildReplay then
    for (rawStr, nm) in targets do
      let modStr := nm.toString
      let replay ← IO.Process.output {
        cmd := app
        args := #["--kernel-replay-module", modStr]
      }
      if replay.exitCode != 0 then
        violations := violations ++ [s!"[TurboLean.KernelReplay] independent kernel re-check of `{rawStr}` failed: kernel replay child exited {replay.exitCode}: {replay.stderr}"]
  for (_, nm) in targets do
    if let some modIdx := env.getModuleIdx? nm then
      if h : modIdx.toNat < env.header.moduleData.size then
        for cinfo in env.header.moduleData[modIdx.toNat].constants do
          allRoots := allRoots.push cinfo.name
  let axMap := collectForbiddenAxiomsByDecl env allRoots patterns stubs
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
          if let some (lhs, rhs) := csimpReplacementPair? env cinfo.type then
            if !cinfo.isTheorem || !csimpAllowed declName then
              csimpCandidates := csimpCandidates.push (declName, lhs, rhs)
          if cinfo.isUnsafe &&
             !isWhitelistedInitExecUnsafe env modIdx cinfo &&
             !((safeUnsafeCallWrapperParent? env modIdx cinfo).any (fun pc => unsafeAllowed pc.name)) &&
             !unsafeAllowed declName then
            violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{declName}` in `{rawStr}` is forbidden"]
          if (cinfo.isPartial || (Lean.Compiler.isUnsafeRecName? declName).isSome) &&
             !isCompilerPartialRecDefn env modIdx cinfo then
            violations := violations ++ [s!"[TurboLean.KernelGate] forged or unpaired _unsafe_rec/partial declaration `{declName}` in `{rawStr}` is forbidden"]
          if (Lean.isExtern env declName || (Lean.Compiler.getImplementedBy? env declName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx declName &&
             !((safeUnsafeCallWrapperBridgeParent? env modIdx declName).any (fun pc => unsafeAllowed pc.name)) &&
             !isPinnedFfiOpaque env ffiAllow modIdx cinfo &&
             !implByAllowed declName then
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on `{declName}` in `{rawStr}` is forbidden"]
          for ax in axMap[declName]?.getD #[] do
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
        if !csimpCandidates.isEmpty then
          let mut targetCompiledCache : Std.HashMap Name (Std.HashSet Name) := {}
          let mut reachCache : Std.HashMap (Name × Name) Bool := {}
          let getTargetCompiled (fnName : Name) : Std.HashSet Name := Id.run do
            if let some s := targetCompiledCache[fnName]? then
              return s
            return collectCompiledCodeConsts env fnName
          for (_, lhs, rhs) in csimpCandidates do
            for fnName in [lhs, rhs] do
              if !targetCompiledCache.contains fnName then
                targetCompiledCache := targetCompiledCache.insert fnName (collectCompiledCodeConsts env fnName)
            for (u, v) in [(lhs, rhs), (rhs, lhs)] do
              if !reachCache.contains (u, v) then
                reachCache := reachCache.insert (u, v) (isKernelConstantReachable env u v)
          let isReachableCached (u v : Name) : Bool :=
            reachCache[(u, v)]?.getD false
          let mut callerNames : Array Name := #[]
          let mut seenCallers : Std.HashSet Name := {}
          for callerInfo in mdata.constants do
            seenCallers := seenCallers.insert callerInfo.name
            callerNames := callerNames.push callerInfo.name
          for bDecl in Lean.Compiler.LCNF.baseExt.getModuleEntries env modIdx do
            if !seenCallers.contains bDecl.name then
              seenCallers := seenCallers.insert bDecl.name
              callerNames := callerNames.push bDecl.name
          for irDecl in Lean.IR.declMapExt.getModuleEntries env modIdx do
            if !seenCallers.contains irDecl.name then
              seenCallers := seenCallers.insert irDecl.name
              callerNames := callerNames.push irDecl.name
          for callerName in callerNames do
            let compiledConsts := collectCompiledCodeConsts env callerName
            if !compiledConsts.isEmpty then
              let ownerInfo? : Option ConstantInfo :=
                match env.find? callerName with
                | some ci => some ci
                | none =>
                  let rec findKernelOwner (nm : Name) : Option ConstantInfo :=
                    match nm with
                    | .str p _ =>
                      if p.isAnonymous then none
                      else match env.find? p with
                        | some ci => some ci
                        | none => findKernelOwner p
                    | .num p _ =>
                      if p.isAnonymous then none
                      else match env.find? p with
                        | some ci => some ci
                        | none => findKernelOwner p
                    | .anonymous => none
                  findKernelOwner callerName
              let ownerName := ownerInfo?.map ConstantInfo.name |>.getD callerName
              let kernelConsts := ownerInfo?.map ConstantInfo.getUsedConstantsAsSet |>.getD {}
              for (thmName, lhs, rhs) in csimpCandidates do
                if ownerName != lhs && ownerName != rhs then
                  let lhsRhs := isReachableCached lhs rhs
                  let rhsLhs := isReachableCached rhs lhs
                  if !(lhsRhs && rhsLhs) then
                    let lhsCompiled := getTargetCompiled lhs
                    let rhsCompiled := getTargetCompiled rhs
                    let inlinedRhs := !rhsCompiled.isEmpty && !lhsCompiled.isEmpty &&
                      rhsCompiled.all (fun c => compiledConsts.contains c) &&
                      !lhsCompiled.all (fun c => compiledConsts.contains c)
                    let inlinedLhs := !lhsCompiled.isEmpty && !rhsCompiled.isEmpty &&
                      lhsCompiled.all (fun c => compiledConsts.contains c) &&
                      !rhsCompiled.all (fun c => compiledConsts.contains c)
                    let fwdHit := !lhsRhs &&
                                  (kernelConsts.isEmpty || (kernelConsts.contains lhs && !kernelConsts.contains rhs)) &&
                                  (compiledConsts.contains rhs || compiledConsts.contains (Lean.Compiler.mkUnsafeRecName rhs) || inlinedRhs)
                    let revHit := !rhsLhs &&
                                  (!kernelConsts.isEmpty && kernelConsts.contains rhs && !kernelConsts.contains lhs) &&
                                  (compiledConsts.contains lhs || compiledConsts.contains (Lean.Compiler.mkUnsafeRecName lhs) ||
                                    (inlinedLhs && !lhsRhs))
                    if fwdHit || revHit then
                      violations := violations ++ [s!"[TurboLean.KernelGate] local csimp replacement `{thmName}` ({lhs} <-> {rhs}) rewrote compiled code of `{callerName}` in `{rawStr}`"]
        for extraName in mdata.extraConstNames do
          if (Lean.isExtern env extraName || (Lean.Compiler.getImplementedBy? env extraName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx extraName &&
             !((safeUnsafeCallWrapperBridgeParent? env modIdx extraName).any (fun pc => unsafeAllowed pc.name)) &&
             !((env.find? extraName).any (isPinnedFfiOpaque env ffiAllow modIdx)) &&
             !implByAllowed extraName then
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on auxiliary `{extraName}` in `{rawStr}` is forbidden"]
      else
        violations := violations ++ [s!"[TurboLean.KernelGate] module `{rawStr}` index out of bounds"]
  let mut seenCSimp : Std.HashMap Name Bool := {}
  let entryTouchesTarget (e : Lean.Compiler.CSimp.Entry) : Bool :=
    [e.thmName, e.fromDeclName, e.toDeclName].any fun nm =>
      match env.getModuleIdxFor? nm with
      | some idx => targetIdxs.contains idx
      | none => false
  let checkCSimpEntry (e : Lean.Compiler.CSimp.Entry) : List String := Id.run do
    if !entryTouchesTarget e then
      return []
    if (env.find? e.thmName).any (·.isTheorem) && csimpAllowed e.thmName then
      return []
    let mut out : List String := []
    let mut seenMod : Std.HashMap ModuleIdx Bool := {}
    for nm in [e.thmName, e.fromDeclName, e.toDeclName] do
      if let some idx := env.getModuleIdxFor? nm then
        if !(seenMod[idx]?.getD false) then
          if let some modLabel := targetIdxs[idx]? then
            seenMod := seenMod.insert idx true
            out := out ++ [s!"[TurboLean.KernelGate] csimp replacement `{e.thmName}` ({e.fromDeclName} -> {e.toDeclName}) touching `{modLabel}` is forbidden"]
    return out
  for (modIdx, _) in targetIdxs.toArray do
    for scEntry in Lean.Compiler.CSimp.ext.ext.getModuleEntries env modIdx do
      let entry := match scEntry with | .global e | .scoped _ e => e
      if !(seenCSimp[entry.thmName]?.getD false) then
        seenCSimp := seenCSimp.insert entry.thmName true
        violations := violations ++ checkCSimpEntry entry
  let globalCSimp := Lean.Compiler.CSimp.ext.getState env
  for (_, entry) in globalCSimp.map do
    if !(seenCSimp[entry.thmName]?.getD false) && entryTouchesTarget entry then
      seenCSimp := seenCSimp.insert entry.thmName true
      violations := violations ++ checkCSimpEntry entry
  let scopedCSimp := (Lean.Compiler.CSimp.ext.ext.getState env).scopedEntries.map
  for (_, entries) in scopedCSimp do
    for entry in entries.toArray do
      if !(seenCSimp[entry.thmName]?.getD false) && entryTouchesTarget entry then
        seenCSimp := seenCSimp.insert entry.thmName true
        violations := violations ++ checkCSimpEntry entry
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
    (skipChildReplay : Bool := false) (allowSorry : Bool := false) : IO (List String) := do
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
    let (vs, _) ← auditImportedModulesInEnv env slice ffiAllow patterns csimpPatterns {} unsafePatterns implByPatterns skipChildReplay allowSorry
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
    let runSubSlice (sub : Array (String × Name)) : IO (List String) := do
      let modFlags := sub.map (·.1)
      let child ← IO.Process.output {
        cmd := app
        args := #["--audit-modules"] ++ replayFlags ++ sorryFlags ++ ffiFlags ++ modFlags
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
    (skipChildReplay : Bool := false) (allowSorry : Bool := false) : IO (Bool × List String) := do
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
  let sliceViolations ← auditModuleSlice parsed ffiAllow skipChildReplay allowSorry
  let allViolations := initViolations ++ sliceViolations
  return (allViolations.isEmpty, allViolations)

private def formatReducibilityStatus (r : ReducibilityStatus) : String :=
  match r with
  | .reducible => "reducible"
  | .semireducible => "semireducible"
  | .irreducible => "irreducible"
  | .implicitReducible => "implicit_reducible"
  | .instanceReducible => "instance_reducible"

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
  || extStr == "Lean.Compiler.LCNF.monoTypeExt"
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
    (∅ : NameMap ImportArtifacts).insert nm (ImportArtifacts.ofArrays #[oleanParts, irParts])
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
  let lcnfMonoTypeEntries := ((Compiler.LCNF.monoTypeExt.getModuleEntries env idx).map fun (dName, mTy) =>
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
  | .ofOriginatingSyntax _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .ofLazy fn _ =>
    let dyn ← (fn none : BaseIO Dynamic)
    if let some inner := dyn.get? MessageData then
      walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | _ => pure ()

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
          let (ok, vs) ← TurboLean.ZygoteWorker.auditCompiledModules mods ffiAllow (!skipReplayFlags.isEmpty) allowSorry
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
  let mut prefixTreeByImport : Std.HashMap String (Array (String × Command.State × List String × String × Nat)) := {}
  -- Environment extensions registered by one import set are not safe to reuse through a
  -- different cached environment. Bind this process to the first `importsCsv` it serves.
  let mut boundImports? : Option String := none
  let mut poisoned := false
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
    let allowStub := modeFlag == "allow_stub" || modeFlag.startsWith "allow_stub:" || isProbeStub ||
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
    else if modeFlag.startsWith "emit_olean:" then
      let metaParts := ((modeFlag.drop 11).toString).splitOn ":"
      let modStr := TurboLean.ZygoteWorker.decodeHexToString (metaParts.headD "")
      let oleanStr := TurboLean.ZygoteWorker.decodeHexToString (metaParts.drop 1 |>.headD "")
      let hexFn := metaParts.drop 2 |>.headD ""
      let fnOpt := if hexFn.isEmpty then none else some (TurboLean.ZygoteWorker.decodeHexToString hexFn)
      let modName := TurboLean.ZygoteWorker.parseModuleName modStr
      let emitOpt := if oleanStr.isEmpty then none else some (modName, System.FilePath.mk oleanStr)
      (fnOpt, none, emitOpt)
    else
      (none, none, none)
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
                  (requiredTargets := some []) (fastMap := fastMap)
              pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts))
          if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs 0 bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed bDeclTypes
        else if isRaceCandidates then
          let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed, rDeclTypes) ←
            TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs (fun cc => do
              let (ok, us, hbs, nodes, errs, msgs, outS, used, dts, _) ←
                TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref cc) allowStub false fn none encodedLeanArgs stubTargets stubs
                  (requiredTargets := some []) (fastMap := fastMap)
              pure (ok, us, hbs, nodes, errs, msgs, outS, used, dts))
          if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs 0 rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed rDeclTypes
        else
          let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts, declTypes, sorryDecls) ←
            TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
              (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
              (allowSorry := allowSorry)
          if !ok && errs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs 0 elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts declTypes sorryDecls
      else
        let fnPref := customFileName?.getD "<zygote-prefix>"
        let cwdKey := targetCwd.toString
        let emitModKey := match emitOlean? with | some (m, _) => m.toString | none => ""
        let prefAllowStub := !evalMode && emitOlean?.isNone && !strictAll
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
                (strictPrefix := !allowStub) (requiredTargets := some []) (fastMap := fastMap)
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
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed, rDeclTypes) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalFromCkpt
              if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit prefixCacheHit importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed rDeclTypes
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
                if allowStub || prefAllowStub || allowSorry || evalMode then
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
            let (ok, elabUs, dHbs, ptNodes, errs, dMsgs, dOut, usedConsts, declTypes, sorryDecls, finalSt) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState bodyCode fn allowStub evalMode stubTargets stubs
                (strictPrefix := strictAll) (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                (allowSorry := allowSorry)
            let mut finalOk := ok
            let mut finalErrs := errs
            if finalOk then
              if let some (modName, oleanPath) := emitOlean? then
                if allowStub || prefAllowStub || allowSorry || evalMode then
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
                  TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalCandCombined (!prefErrs.isEmpty)
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
              let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts, declTypes, sorryDecls) ←
                TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub evalMode fn emitOlean? encodedLeanArgs stubTargets stubs
                  (requiredTargets := some requiredTargets) (fastMap := fastMap) (includeStubsInDeclTypes := isProbeStub)
                  (allowSorry := allowSorry)
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
