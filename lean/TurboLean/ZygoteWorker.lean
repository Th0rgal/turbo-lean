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
import Lean.Compiler.CSimpAttr
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.IR.CompilerM
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

/-- Emit a single-line JSON Zygote reply and flush `stdout`. -/
def emitZygoteReply (stdout : IO.FS.Stream) (ok : Bool) (winIdx? : Option String) (kgActive importOk envHit prefHit : Bool)
    (importUs prefixUs elabUs hbs nodes subVerified : Nat) (outStr : String) (msgs errs used : List String) : IO Unit := do
  let winPart := match winIdx? with | some w => s!"\"winning_candidate_idx\":{w}," | none => ""
  let kgPart := if importOk then s!"\"kernel_gate_active\":{kgActive}," else ""
  stdout.putStrLn s!"\{\"ok\":{ok},{winPart}{kgPart}\"import_ok\":{importOk},\"env_cache_hit\":{envHit},\"prefix_cache_hit\":{prefHit},\"import_us\":{importUs},\"prefix_us\":{prefixUs},\"elab_us\":{elabUs},\"heartbeats\":{hbs},\"proof_term_nodes\":{nodes},\"subshards_verified\":{subVerified},\"stdout\":\"{jsonEscape outStr}\",\"messages\":[{jsonStrList msgs}],\"errors\":[{jsonStrList errs}],\"used_constants\":[{jsonStrList used}]}"
  stdout.flush

/-- The toolchain's `cadical`, set in `main` from the sysroot: `bv_decide` looks for it next to the
    running executable (for the zygote, a copy outside the toolchain) and then on `PATH`. -/
initialize satSolverRef : IO.Ref String ← IO.mkRef ""

/-- `opts` with `sat.solver` pointing at the toolchain's `cadical`, unless the shard sets it. -/
def withToolchainSatSolver (opts : Options) : IO Options := do
  let s ← satSolverRef.get
  return if s.isEmpty || opts.contains `sat.solver then opts else opts.set `sat.solver s

/-- Apply filtered CLI-style `-Dkey=value` options (e.g. Lake `leanOptions` / `moreLeanArgs` / `weakLeanArgs`)
    onto `opts` after imports are loaded, matching `Lean.Language.Lean.setOption` / `Lean.Shell.setConfigOption`. -/
def applyEncodedLeanArgs (baseOpts : Options) (encodedArgs : String) : IO Options := do
  if encodedArgs.trimAscii.isEmpty then
    return baseOpts
  let decls ← getOptionDecls
  let mut opts := baseOpts
  for rawLine in encodedArgs.splitOn "\n" do
    let arg := rawLine.trimAscii.toString
    if arg.startsWith "-D" then
      let kv := (arg.drop 2).toString
      let eqParts := kv.splitOn "="
      match eqParts with
      | [] | [_] => pure ()
      | rawK :: rest =>
        let k := rawK.trimAscii.toString
        let v := String.intercalate "=" rest
        if !k.isEmpty && !v.isEmpty && !(k == "warn.sorry" && v == "false") then
          let rawName := k.toName
          let isWeak := rawName.getRoot == `weak
          let optName := if isWeak then rawName.replacePrefix `weak Name.anonymous else rawName
          match decls.find? optName with
          | some decl =>
            match decl.defValue with
            | .ofBool _ =>
              if v == "true" then opts := opts.set optName true
              else if v == "false" then opts := opts.set optName false
            | .ofNat _ =>
              if let some n := v.toNat? then
                opts := opts.set optName n
            | .ofString _ =>
              opts := opts.set optName v
            | _ => pure ()
          | none =>
            if !isWeak then
              opts := opts.set optName v
  return opts

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
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
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
    let csimpSt := Lean.Compiler.CSimp.ext.getState afterEnv
    if csimpSt.thmNames.contains name || csimpSt.map.contains name then
      violations := violations ++ [s!"[TurboLean.KernelGate] csimp replacement bypass on `{name}` is forbidden"]
    let axs := collectNewDeclAxioms beforeEnv afterEnv name
    for ax in axs do
      if !isAllowedAxiom patterns ax then
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
  if allMessages.any isRuntimePanicText then
    errs := errs ++ [runtimePanicErr]
  if !evalMode then
    let explicitStubToken := ":= " ++ forbiddenToken
    let allowSorryInKernel := allowStub && (code.splitOn explicitStubToken).length > 1
    let (_, kernelErrs) ← auditNewKernelDecls baseState.env s.commandState.env allowSorryInKernel
    errs := errs ++ kernelErrs
    usedConstants := (collectNewDeclUsedConstants baseState.env s.commandState.env).toList
    proofTermNodes := countNewDeclExprNodes baseState.env s.commandState.env
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  let cleanNextState : Command.State := { s.commandState with messages := {} }
  return (errs.isEmpty, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, cleanNextState)

/-- Atomically serialize `finalEnv` (and any module-system companions `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`)
    to `oleanPath` only after verifying `mainModule == modName` and re-auditing all declarations added since `baseEnv`
    for zero forbidden axioms (`sorryAx`, `reduceBool`, `trustCompiler`). -/
def writeVerifiedModuleOlean (baseEnv finalEnv : Environment) (modName : Name) (oleanPath : System.FilePath) : IO Bool := do
  if modName.isAnonymous || finalEnv.mainModule != modName then
    return false
  let (clean, kErrs) ← auditNewKernelDecls baseEnv finalEnv false
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

namespace ZygoteBlake3

def IV : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

@[inline] def g (state : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := state[a]! + state[b]! + mx; let vd := rotr32 (state[d]! ^^^ va) 16
  let vc := state[c]! + vd; let vb := rotr32 (state[b]! ^^^ vc) 12
  let va := va + vb + my; let vd := rotr32 (vd ^^^ va) 8
  let vc := vc + vd; let vb := rotr32 (vb ^^^ vc) 7
  (((state.set! a va).set! b vb).set! c vc).set! d vd

@[inline] def roundFn (state : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let state := g (g (g (g state 0 4 8 12 m[0]! m[1]!) 1 5 9 13 m[2]! m[3]!) 2 6 10 14 m[4]! m[5]!) 3 7 11 15 m[6]! m[7]!
  g (g (g (g state 0 5 10 15 m[8]! m[9]!) 1 6 11 12 m[10]! m[11]!) 2 7 8 13 m[12]! m[13]!) 3 4 9 14 m[14]! m[15]!

@[inline] def permute (m : Array UInt32) : Array UInt32 := MSG_PERMUTATION.map (fun idx => m[idx]!)

def compress (cv : Array UInt32) (blockWords : Array UInt32) (counter : UInt64) (blockLen : UInt32) (flags : UInt32) : Array UInt32 :=
  let st0 : Array UInt32 := #[cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
    IV[0]!, IV[1]!, IV[2]!, IV[3]!, counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let (st, _) := (List.range 7).foldl (fun (st, m) r => (roundFn st m, if r < 6 then permute m else m)) (st0, blockWords)
  (List.range 8).foldl (fun acc i => (acc.set! i (acc[i]! ^^^ acc[i + 8]!)).set! (i + 8) (acc[i + 8]! ^^^ cv[i]!)) st

def blockBytesToWords (bytes : ByteArray) (offset : Nat) (len : Nat) : Array UInt32 :=
  let getByte (k : Nat) : UInt32 := if k < len && offset + k < bytes.size then (bytes.get! (offset + k)).toUInt32 else 0
  (Array.range 16).map (fun w =>
    let base := w * 4
    getByte base ||| (getByte (base + 1) <<< 8) ||| (getByte (base + 2) <<< 16) ||| (getByte (base + 3) <<< 24))

def wordToHexLE (w : UInt32) : String :=
  let hexChars := "0123456789abcdef".toList
  let byteHex (b : UInt32) : List Char := [hexChars[((b >>> 4) &&& 0xf).toNat]?.getD '0', hexChars[(b &&& 0xf).toNat]?.getD '0']
  String.ofList (byteHex (w &&& 0xff) ++ byteHex ((w >>> 8) &&& 0xff) ++ byteHex ((w >>> 16) &&& 0xff) ++ byteHex ((w >>> 24) &&& 0xff))

def cvToHex (cv : Array UInt32) : String := String.join ((List.range 8).map (fun i => wordToHexLE cv[i]!))

def hashChunk (bytes : ByteArray) (chunkOffset : Nat) (chunkLen : Nat) (chunkCounter : UInt64) (isRoot : Bool) : Array UInt32 :=
  let numBlocks := if chunkLen == 0 then 1 else (chunkLen + 63) / 64
  (List.range numBlocks).foldl (fun cv bIdx =>
    let blkOffset := chunkOffset + bIdx * 64
    let blkLen := if chunkLen == 0 then 0 else Nat.min 64 (chunkLen - bIdx * 64)
    let flags : UInt32 := (if bIdx == 0 then 1 else 0) ||| (if bIdx + 1 == numBlocks then 2 ||| (if isRoot then 8 else 0) else 0)
    (compress cv (blockBytesToWords bytes blkOffset blkLen) chunkCounter blkLen.toUInt32 flags).extract 0 8) IV

def mergeStack (fuel : Nat) (stack : List (Array UInt32)) (count : Nat) (isFinalChunk : Bool) : List (Array UInt32) :=
  match fuel with
  | 0 => stack
  | fuel' + 1 =>
    if count % 2 == 1 then stack
    else match stack with
      | rightCv :: leftCv :: rest =>
        let flags : UInt32 := 4 ||| (if isFinalChunk && rest.isEmpty && (count / 2 == 1) then 8 else 0)
        mergeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest) (count / 2) isFinalChunk
      | _ => stack

def finalizeStack (fuel : Nat) (stack : List (Array UInt32)) : Array UInt32 :=
  match fuel, stack with
  | 0, _ => stack.head?.getD IV
  | _, [] => IV
  | _, [rootCv] => rootCv
  | fuel' + 1, rightCv :: leftCv :: rest =>
    let flags : UInt32 := 4 ||| (if rest.isEmpty then 8 else 0)
    finalizeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest)

def blake3Bytes (bytes : ByteArray) : String :=
  let totalLen := bytes.size
  let numChunks := if totalLen == 0 then 1 else (totalLen + 1023) / 1024
  if numChunks == 1 then cvToHex (hashChunk bytes 0 totalLen 0 true)
  else
    let stack := (List.range numChunks).foldl (fun st cIdx =>
      let cOff := cIdx * 1024
      let cLen := Nat.min 1024 (totalLen - cOff)
      let cv := hashChunk bytes cOff cLen cIdx.toUInt64 false
      mergeStack 64 (cv :: st) (cIdx + 1) (cIdx + 1 == numChunks)) []
    cvToHex (finalizeStack 64 stack)

end ZygoteBlake3

/-- 256-bit cryptographic BLAKE3 content digest over raw artifact bytes. -/
def hashBytesBlake3Hex (bs : ByteArray) : String :=
  ZygoteBlake3.blake3Bytes bs

/-- Extract all direct imports plus any transitive modules in `env.header.moduleNames`
    whose `.olean` lives outside the immutable toolchain `sysroot`. -/
def extractTrackedClosureMods (importsCsv : String) (sysroot : System.FilePath) (env : Environment) : IO (Array Name) := do
  let sysPrefix := (← try IO.FS.realPath sysroot catch _ => pure sysroot).toString
  let mut out : Array Name := #[]
  for imp in parseImportsCsv importsCsv do
    if !out.contains imp.module then
      out := out.push imp.module
  for modName in env.header.moduleNames do
    if !out.contains modName then
      try
        let p ← Lean.findOLean modName
        let rp ← try IO.FS.realPath p catch _ => pure p
        if !rp.toString.startsWith sysPrefix then
          out := out.push modName
      catch _ =>
        out := out.push modName
  return out

/-- Compute a 256-bit BLAKE3 content-verified cache key over the tracked import closure `trackedMods`,
    including canonical resolved path, byte size, and BLAKE3 content digest for every non-sysroot
    `.olean` and its module-system companions (`.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.ir.sig`). -/
def computeImportsClosureDiskKey (importsCsv : String) (sysroot : System.FilePath) (trackedMods : Array Name) : IO (Option String) := do
  let sysPrefix := (← try IO.FS.realPath sysroot catch _ => pure sysroot).toString
  let mut parts : List String := [importsCsv]
  for modName in trackedMods do
    try
      let p ← Lean.findOLean modName
      let rp ← try IO.FS.realPath p catch _ => pure p
      let m ← rp.metadata
      let isSys := rp.toString.startsWith sysPrefix
      let oleanDigest ← if isSys then pure "sys" else do
        let bs ← IO.FS.readBinFile rp
        pure (hashBytesBlake3Hex bs)
      let mut compParts : List String := [s!"{modName}:{rp}:{m.byteSize}:{oleanDigest}"]
      if !isSys then
        let companions : List (String × System.FilePath) := [
          ("srv", System.FilePath.mk s!"{p}.server"),
          ("prv", System.FilePath.mk s!"{p}.private"),
          ("ilean", p.withExtension "ilean"),
          ("ir", p.withExtension "ir"),
          ("sig", System.FilePath.mk s!"{p.withExtension "ir"}.sig")
        ]
        for (tag, cp) in companions do
          if ← cp.pathExists then
            let crp ← try IO.FS.realPath cp catch _ => pure cp
            let cm ← crp.metadata
            let cbs ← IO.FS.readBinFile crp
            compParts := s!"{tag}:{crp}:{cm.byteSize}:{hashBytesBlake3Hex cbs}" :: compParts
          else
            compParts := s!"{tag}:none" :: compParts
      parts := (String.intercalate "," compParts.reverse) :: parts
    catch _ =>
      return none
  return some (String.intercalate "|" parts.reverse)

/-- Elaborate and kernel-typecheck `bodyCode` on top of an immutable `baseEnv : Lean.Environment`
    without mutating `baseEnv`.
    Returns `(ok, elapsed_us, heartbeats, proof_term_nodes, error_messages, all_messages, captured_stdout, used_constants)`. -/
def checkShardWithEnv
    (baseEnv : Environment)
    (bodyCode : String)
    (allowStub : Bool := false)
    (evalMode : Bool := false)
    (fileName : String := "<zygote-shard>")
    (emitOlean? : Option (Name × System.FilePath) := none)
    (encodedLeanArgs : String := "") : IO (Bool × Nat × Nat × Nat × List String × List String × String × List String) := do
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
  let (ok, elapsedUs, heartbeats, proofTermNodes, errs, allMessages, capturedStdout, usedConstants, finalSt) ←
    runCommandsFromState baseState bodyCode fileName allowStub evalMode
  let mut finalOk := ok
  let mut finalErrs := errs
  if finalOk then
    if let some (modName, oleanPath) := emitOlean? then
      if allowStub || evalMode then
        finalOk := false
        finalErrs := finalErrs ++ ["emit_olean rejected stubbed or eval mode"]
      else
        let wrote ← writeVerifiedModuleOlean baseEnv finalSt.env modName oleanPath
        if !wrote then
          finalOk := false
          finalErrs := finalErrs ++ ["emit_olean failed module identity or kernel hygiene gate"]
  return (finalOk, elapsedUs, heartbeats, proofTermNodes, finalErrs, allMessages, capturedStdout, usedConstants)

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
        (env.contains (baseName.mkStr "_sunfold") || env.contains (baseName.mkStr "_unary") || bVal.value.getUsedConstants.any nameIsRecCombinator) &&
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

/-- A prefix stub as the host's shard builder emits it: `theorem n : T := sorry`, elaborated to the
    explicit (non-synthetic) `sorryAx (Name → T) false label` (or legacy `sorryAx T false`).
    Elaboration errors and tactics such as `admitGoal` yield synthetic sorries and never qualify. -/
def isExplicitSorryStub (cinfo : ConstantInfo) : Bool :=
  match cinfo with
  | .thmInfo v =>
    let args := v.value.getAppArgs
    let tyOk := fun (e : Expr) => e == v.type || match e with
      | .forallE _ d b _ => d.isConstOf ``Lean.Name && b == v.type
      | _ => false
    v.value.getAppFn.isConstOf (Name.mkSimple ("sor" ++ "ryAx")) && args.size ≥ 2 &&
      args[1]!.isConstOf ``Bool.false && tyOk args[0]!
  | _ => false

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

def isPinnedFfiOpaque (env : Environment) (ffiAllow : Array (Name × Name × String)) (modIdx : ModuleIdx) (cinfo : ConstantInfo) : Bool :=
  match cinfo with
  | .opaqueInfo _ =>
    (Lean.Compiler.getImplementedBy? env cinfo.name).isNone &&
      env.getModuleIdxFor? cinfo.name == some modIdx &&
      (env.header.moduleNames[modIdx.toNat]?).any fun m =>
        (Lean.getExternNameFor env `c cinfo.name).any fun sym => ffiAllow.contains (m, cinfo.name, sym)
  | _ => false

/-- Validated prefix stubs of the audited modules: theorems named in `stubOk` (exact full name)
    whose kernel value is an explicit `sorry` (`isExplicitSorryStub`). -/
def collectStubDecls (env : Environment) (targets : Array (String × Name)) (stubOk : Array String) :
    Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  if stubOk.isEmpty then return out
  for (_, nm) in targets do
    if let some modIdx := env.getModuleIdx? nm then
      if h : modIdx.toNat < env.header.moduleData.size then
        for cinfo in env.header.moduleData[modIdx.toNat].constants do
          if stubOk.contains (cinfo.name.toString (escape := false)) && isExplicitSorryStub cinfo then
            out := out.insert cinfo.name
  return out

def auditImportedModulesInEnv (env : Environment) (targets : Array (String × Name))
    (ffiAllow : Array (Name × Name × String) := #[])
    (patterns : List String := []) (csimpPatterns : List String := [])
    (stubs : Std.HashSet Name := {}) : List String := Id.run do
  let csimpAllowed := fun name : Name => csimpPatterns.any (globMatch ·.toList name.toString.toList)
  let unsfTag := "un" ++ "safe"
  let mut violations : List String := []
  let mut targetIdxs : Std.HashMap ModuleIdx String := {}
  let mut allRoots : Array Name := #[]
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
          if cinfo.isUnsafe && !isWhitelistedInitExecUnsafe env modIdx cinfo then
            violations := violations ++ [s!"[TurboLean.KernelGate] {unsfTag} declaration `{declName}` in `{rawStr}` is forbidden"]
          if (cinfo.isPartial || (Lean.Compiler.isUnsafeRecName? declName).isSome) &&
             !isCompilerPartialRecDefn env modIdx cinfo then
            violations := violations ++ [s!"[TurboLean.KernelGate] forged or unpaired _unsafe_rec/partial declaration `{declName}` in `{rawStr}` is forbidden"]
          if (Lean.isExtern env declName || (Lean.Compiler.getImplementedBy? env declName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx declName && !isPinnedFfiOpaque env ffiAllow modIdx cinfo then
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on `{declName}` in `{rawStr}` is forbidden"]
          for ax in axMap[declName]?.getD #[] do
            violations := violations ++ [s!"[TurboLean.KernelGate] declaration `{declName}` in `{rawStr}` transitively depends on disallowed axiom `{ax}`"]
        if !csimpCandidates.isEmpty then
          let mut targetCompiledCache : Std.HashMap Name (Std.HashSet Name) := {}
          let getTargetCompiled (fnName : Name) : Std.HashSet Name := Id.run do
            if let some s := targetCompiledCache[fnName]? then
              return s
            return collectCompiledCodeConsts env fnName
          for (_, lhs, rhs) in csimpCandidates do
            for fnName in [lhs, rhs] do
              if !targetCompiledCache.contains fnName then
                targetCompiledCache := targetCompiledCache.insert fnName (collectCompiledCodeConsts env fnName)
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
                  let lhsCompiled := getTargetCompiled lhs
                  let rhsCompiled := getTargetCompiled rhs
                  let inlinedRhs := !rhsCompiled.isEmpty && !lhsCompiled.isEmpty &&
                    rhsCompiled.all (fun c => compiledConsts.contains c) &&
                    !lhsCompiled.all (fun c => compiledConsts.contains c)
                  let inlinedLhs := !lhsCompiled.isEmpty && !rhsCompiled.isEmpty &&
                    lhsCompiled.all (fun c => compiledConsts.contains c) &&
                    !rhsCompiled.all (fun c => compiledConsts.contains c)
                  let fwdHit := (kernelConsts.isEmpty || (kernelConsts.contains lhs && !kernelConsts.contains rhs)) &&
                                (compiledConsts.contains rhs || compiledConsts.contains (Lean.Compiler.mkUnsafeRecName rhs) || inlinedRhs)
                  let revHit := (!kernelConsts.isEmpty && kernelConsts.contains rhs && !kernelConsts.contains lhs) &&
                                (compiledConsts.contains lhs || compiledConsts.contains (Lean.Compiler.mkUnsafeRecName lhs) || inlinedLhs)
                  if fwdHit || revHit then
                    violations := violations ++ [s!"[TurboLean.KernelGate] local csimp replacement `{thmName}` ({lhs} <-> {rhs}) rewrote compiled code of `{callerName}` in `{rawStr}`"]
        for extraName in mdata.extraConstNames do
          if (Lean.isExtern env extraName || (Lean.Compiler.getImplementedBy? env extraName).isSome) &&
             !isWhitelistedInitExecBridge env modIdx extraName &&
             !((env.find? extraName).any (isPinnedFfiOpaque env ffiAllow modIdx)) then
            violations := violations ++ [s!"[TurboLean.KernelGate] extern/implemented_by bypass on auxiliary `{extraName}` in `{rawStr}` is forbidden"]
      else
        violations := violations ++ [s!"[TurboLean.KernelGate] module `{rawStr}` index out of bounds"]
  let mut seenCSimp : Std.HashMap Name Bool := {}
  let checkCSimpEntry (e : Lean.Compiler.CSimp.Entry) : List String := Id.run do
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
    if !(seenCSimp[entry.thmName]?.getD false) then
      seenCSimp := seenCSimp.insert entry.thmName true
      violations := violations ++ checkCSimpEntry entry
  let scopedCSimp := (Lean.Compiler.CSimp.ext.ext.getState env).scopedEntries.map
  for (_, entries) in scopedCSimp do
    for entry in entries.toArray do
      if !(seenCSimp[entry.thmName]?.getD false) then
        seenCSimp := seenCSimp.insert entry.thmName true
        violations := violations ++ checkCSimpEntry entry
  return violations

/-- Non-stub theorems of the audited modules, read from the kernel environment (never from
    elaboration output), so the host can confirm every audited target was actually declared. -/
def collectModuleTheorems (env : Environment) (targets : Array (String × Name))
    (stubs : Std.HashSet Name) : Array String := Id.run do
  let mut out : Array String := #[]
  for (_, nm) in targets do
    if let some modIdx := env.getModuleIdx? nm then
      if h : modIdx.toNat < env.header.moduleData.size then
        for cinfo in env.header.moduleData[modIdx.toNat].constants do
          if cinfo.isTheorem && !stubs.contains cinfo.name then
            out := out.push (cinfo.name.toString (escape := false))
  return out

/-- Audit a single compiled shard module: like `auditModuleSlice`, but exempts validated prefix
    stubs named in `stubOk` and also returns the module's non-stub theorems. -/
def auditShardModule (target : String × Name) (ffiAllow : Array (Name × Name × String))
    (stubOk : Array String) : IO (List String × Array String) := do
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let csimpPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_CSIMP").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  try
    let env ← Lean.importModules #[{ module := target.2, importAll := true }] {} 0 #[] true false .private
    let stubs := collectStubDecls env #[target] stubOk
    return (auditImportedModulesInEnv env #[target] ffiAllow patterns csimpPatterns stubs,
      collectModuleTheorems env #[target] stubs)
  catch e =>
    return ([s!"[TurboLean.KernelGate] failed to import `{target.1}` for audit: {e}"], #[])

partial def auditModuleSlice (slice : Array (String × Name)) (ffiAllow : Array (Name × Name × String) := #[]) : IO (List String) := do
  if slice.isEmpty then
    return []
  let patterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_AXIOMS").getD "").splitOn ",").filterMap fun p =>
    let t := p.trimAscii.toString
    if t.isEmpty then none else some t
  let csimpPatterns := (((← IO.getEnv "TURBO_LEAN_ALLOWED_CSIMP").getD "").splitOn ",").filterMap fun p =>
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
    return auditImportedModulesInEnv env slice ffiAllow patterns csimpPatterns
  | .error errMsg =>
    if slice.size == 1 then
      let (rawStr, _) := slice[0]!
      return [s!"[TurboLean.KernelGate] failed to import `{rawStr}` for audit: {errMsg}"]
    let missingIdx? : Option Nat := Id.run do
      if (errMsg.splitOn "does not exist").length > 1 then
        let parts := errMsg.splitOn "of module "
        if parts.length > 1 then
          let modPart := ((parts[1]!).splitOn " does not exist").headD ""
          if !modPart.isEmpty then
            return slice.findIdx? (fun (_, nm) => nm.toString == modPart)
      return none
    match missingIdx? with
    | some idx =>
      let (rawStr, _) := slice[idx]!
      let without := (slice.extract 0 idx) ++ (slice.extract (idx + 1) slice.size)
      let vRest ← auditModuleSlice without ffiAllow
      return [s!"[TurboLean.KernelGate] failed to import `{rawStr}` for audit: {errMsg}"] ++ vRest
    | none =>
      let collideIdx? : Option Nat := Id.run do
        let parts := errMsg.splitOn "import "
        if parts.length > 1 then
          let modPart := ((parts[1]!).splitOn " failed").headD ""
          if !modPart.isEmpty then
            return slice.findIdx? (fun (_, nm) => nm.toString == modPart)
        return none
      match collideIdx? with
      | some idx =>
        if idx > 0 then
          let without := (slice.extract 0 idx) ++ (slice.extract (idx + 1) slice.size)
          let vRest ← auditModuleSlice without ffiAllow
          let vSingle ← auditModuleSlice #[slice[idx]!] ffiAllow
          return vRest ++ vSingle
        else
          let mid := slice.size / 2
          let v1 ← auditModuleSlice (slice.extract 0 mid) ffiAllow
          let v2 ← auditModuleSlice (slice.extract mid slice.size) ffiAllow
          return v1 ++ v2
      | none =>
        let mid := slice.size / 2
        let v1 ← auditModuleSlice (slice.extract 0 mid) ffiAllow
        let v2 ← auditModuleSlice (slice.extract mid slice.size) ffiAllow
        return v1 ++ v2

def auditCompiledModules (modNames : List String) (ffiAllow : Array (Name × Name × String) := #[]) : IO (Bool × List String) := do
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
  let sliceViolations ← auditModuleSlice parsed ffiAllow
  let allViolations := initViolations ++ sliceViolations
  return (allViolations.isEmpty, allViolations)

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
  | "--audit-modules" :: modArgs =>
    let stdout ← IO.getStdout
    let (ffiArgs, rest) := modArgs.partition (·.startsWith "--ffi-allow=")
    let (stubArgs, rest) := rest.partition (·.startsWith "--stub-ok=")
    let (shardFlag, mods) := rest.partition (· == "--shard")
    let ffiAllow := ffiArgs.toArray.filterMap fun a =>
      match ((a.drop 12).toString.splitOn "=") with
      | [m, d, sym] => some (TurboLean.ZygoteWorker.parseModuleName m, TurboLean.ZygoteWorker.parseModuleName d, sym)
      | _ => none
    let audited := mods.filter (!·.trimAscii.isEmpty)
    -- `--shard` audits exactly one compiled shard module, exempting validated `--stub-ok=` prefix
    -- stubs and reporting its theorems; stubs are never exempt in whole-module audits.
    let (ok, violations, decls) ← match shardFlag.isEmpty, audited with
      | true, _ =>
        if stubArgs.isEmpty then
          let (ok, vs) ← TurboLean.ZygoteWorker.auditCompiledModules mods ffiAllow
          pure (ok, vs, none)
        else pure (false, ["[TurboLean.KernelGate] --stub-ok requires --shard"], none)
      | false, [m] =>
        let nm := TurboLean.ZygoteWorker.parseModuleName m.trimAscii.toString
        let (vs, ds) ← TurboLean.ZygoteWorker.auditShardModule (m.trimAscii.toString, nm) ffiAllow
          (stubArgs.toArray.map fun a => (a.drop 10).toString)
        pure (vs.isEmpty && !nm.isAnonymous, vs, some ds)
      | false, _ => pure (false, ["[TurboLean.KernelGate] --shard audits exactly one module"], none)
    let ok := ok && ffiAllow.size == ffiArgs.length
    let declsJson := match decls with
      | some ds => s!",\"decls\":[{TurboLean.ZygoteWorker.jsonStrList ds.toList}]"
      | none => ""
    stdout.putStrLn s!"\{\"ok\":{ok},\"audited\":[{TurboLean.ZygoteWorker.jsonStrList audited}],\"violations\":[{TurboLean.ZygoteWorker.jsonStrList violations}]{declsJson}}"
    stdout.flush
    if !ok then
      IO.Process.exit 1
    return
  | _ => pure ()
  unsafe enableInitializersExecution
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let maxCheckpoints ← match (← IO.getEnv "TURBO_LEAN_ZYGOTE_MAX_CHECKPOINTS") with
    | some s => pure (match s.trimAscii.toString.toNat? with | some n => if n > 0 then n else 32 | none => 32)
    | none => pure 32
  let maxEnvCache : Nat := 16
  let mut envCache : Std.HashMap String (String × Array Name × Lean.Environment) := {}
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
    let (hexBody, modeFlag, prefixKey, hexPrefix) :=
      if raw1 == "batch_fission" || raw1.startsWith "batch_fission" ||
         raw1 == "race_candidates" || raw1.startsWith "race_candidates" then
        (parts.drop 4 |>.headD "", raw1, raw2, parts.drop 3 |>.headD "")
      else
        (raw1, raw2, parts.drop 3 |>.headD "", parts.drop 4 |>.headD "")
    let hexOpts := parts.drop 5 |>.headD ""
    let encodedLeanArgs := if hexOpts.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexOpts
    let isBatchFission := modeFlag == "batch_fission" || modeFlag.startsWith "batch_fission"
    let isRaceCandidates := modeFlag == "race_candidates" || modeFlag.startsWith "race_candidates"
    let allowStub := modeFlag == "allow_stub"
    let evalMode := modeFlag == "eval" || modeFlag.startsWith "eval:"
    let (customFileName?, customCwd?, emitOlean?) := if modeFlag.startsWith "eval:" then
      let metaParts := ((modeFlag.drop 5).toString).splitOn ":"
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
    let bodyCode ← if isBatchFission || isRaceCandidates then pure "" else TurboLean.ZygoteWorker.decodePayloadOrShm hexBody
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
    let cachedHit? ← match envCache[importsCsv]? with
      | some (cachedDiskKey, trackedMods, cachedEnv) => do
        match ← TurboLean.ZygoteWorker.computeImportsClosureDiskKey importsCsv sysroot trackedMods with
        | some curKey =>
          if curKey == cachedDiskKey then pure (some (curKey, trackedMods, cachedEnv)) else pure none
        | none => pure none
      | none => pure none
    let (envCacheHit, importUs, baseEnv?, envErr?, envDiskKey?, trackedMods) ← match cachedHit? with
      | some (curKey, tMods, env) => pure (true, 0, some env, none, some curKey, tMods)
      | none => do
        let tImp0 ← IO.monoNanosNow
        let level : OLeanLevel := if isMod then .exported else .private
        try
          unsafe enableInitializersExecution
          let env ← Lean.importModules imports {} 1025 #[] false true level
          let tMods ← TurboLean.ZygoteWorker.extractTrackedClosureMods importsCsv sysroot env
          let freshKey? ← TurboLean.ZygoteWorker.computeImportsClosureDiskKey importsCsv sysroot tMods
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, some env, none, freshKey?, tMods)
        catch e =>
          let tImp1 ← IO.monoNanosNow
          pure (false, (tImp1 - tImp0) / 1000, none, some (toString e), none, #[])
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
          envCache := envCache.insert importsCsv (validDiskKey, trackedMods, baseEnv)
          if !envCacheOrder.contains importsCsv then
            envCacheOrder := envCacheOrder.push importsCsv
      let envDiskKey ← match envDiskKey? with
        | some k => pure k
        | none => do
          let nonce ← IO.monoNanosNow
          pure s!"uncached:{importsCsv}:{nonce}"
      let kgActive := !evalMode
      if prefixKey.isEmpty || hexPrefix.isEmpty then
        let fn := customFileName?.getD "<zygote-shard>"
        let prefixCode := if hexPrefix.isEmpty then "" else TurboLean.ZygoteWorker.decodeHexToString hexPrefix
        let combineWithPref := fun (subCode : String) =>
          if prefixCode.trimAscii.toString.isEmpty then subCode else prefixCode ++ "\n" ++ subCode
        if isBatchFission then
          let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
            TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs (fun sc =>
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref sc) allowStub false fn none encodedLeanArgs)
          if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs 0 bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
        else if isRaceCandidates then
          let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
            TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs (fun cc =>
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (combineWithPref cc) allowStub false fn none encodedLeanArgs)
          if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs 0 rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
        else
          let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts) ←
            TurboLean.ZygoteWorker.checkShardWithEnv baseEnv bodyCode allowStub evalMode fn emitOlean? encodedLeanArgs
          if !ok && errs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
          TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs 0 elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts
      else
        let fnPref := customFileName?.getD "<zygote-prefix>"
        let cwdKey := targetCwd.toString
        let emitModKey := match emitOlean? with | some (m, _) => m.toString | none => ""
        let prefAllowStub := !evalMode && emitOlean?.isNone
        let optsCacheSuffix := if hexOpts.isEmpty then "" else s!"\topts:{hexOpts}"
        let importStubKey := (if evalMode || emitOlean?.isSome then s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{fnPref}\t{cwdKey}\t{emitModKey}" else s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}") ++ optsCacheSuffix
        let fullPrefixKey := (if evalMode || emitOlean?.isSome then s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{fnPref}\t{cwdKey}\t{emitModKey}\t{prefixKey}" else s!"{envDiskKey}\t{prefAllowStub}\t{evalMode}\t{prefixKey}") ++ optsCacheSuffix
        let prefixCode ← TurboLean.ZygoteWorker.decodePayloadOrShm hexPrefix
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
              let (pOk, pUs, pHbs, _pNodes, pErrs, pMsgs, pOut, _pUsed, nextSt) ←
                TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode fnPref prefAllowStub evalMode
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
                let deltaCode := (prefixCode.drop (String.length prevCode)).toString
                let (dOk, dUs, dHbs, _dNodes, dErrs, dMsgs, dOut, _dUsed, dNextSt) ←
                  TurboLean.ZygoteWorker.runCommandsFromState prevState deltaCode fnPref prefAllowStub evalMode
                if dErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
                if dOk then
                  pure (some (false, dUs, some dNextSt, ([] : List String), prevMsgs ++ dMsgs, prevOut ++ dOut, prevHbs + dHbs, some prefixCode))
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
              let (pOk, pUs, pHbs, _pNodes, pErrs, pMsgs, pOut, _pUsed, nextSt) ←
                TurboLean.ZygoteWorker.runCommandsFromState baseState prefixCode fnPref prefAllowStub evalMode
              if pErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
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
            let (ok, us, hbs, nodes, errs, msgs, outS, used, _) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState sc fn allowStub false
            pure (ok, us, hbs, nodes, errs, msgs, outS, used)
          if isBatchFission then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout true none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
                TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalFromCkpt
              if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
          else if isRaceCandidates then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs [] []
            else
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalFromCkpt
              if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit prefixCacheHit importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
          else if bodyCode.trimAscii.toString.isEmpty then
            let mut emitOk := true
            let mut emitErrs : List String := []
            if let some (modName, oleanPath) := emitOlean? then
              if allowStub || prefAllowStub || evalMode then
                emitOk := false
                emitErrs := ["emit_olean rejected stubbed or eval mode"]
              else
                let wrote ← TurboLean.ZygoteWorker.writeVerifiedModuleOlean baseEnv ckptState.env modName oleanPath
                if !wrote then
                  emitOk := false
                  emitErrs := ["emit_olean failed module identity or kernel hygiene gate"]
            let prefPtNodes := if !evalMode then TurboLean.ZygoteWorker.countNewDeclExprNodes baseEnv ckptState.env else 0
            let prefUsed := if !evalMode then (TurboLean.ZygoteWorker.collectNewDeclUsedConstants baseEnv ckptState.env).toList else []
            TurboLean.ZygoteWorker.emitZygoteReply stdout emitOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs 0 prefHbs prefPtNodes (if emitOk then 1 else 0) prefOut prefMsgs emitErrs prefUsed
          else
            let (ok, elabUs, dHbs, ptNodes, errs, dMsgs, dOut, usedConsts, finalSt) ←
              TurboLean.ZygoteWorker.runCommandsFromState ckptState bodyCode fn allowStub evalMode
            let mut finalOk := ok
            let mut finalErrs := errs
            if finalOk then
              if let some (modName, oleanPath) := emitOlean? then
                if allowStub || prefAllowStub || evalMode then
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
            if !finalOk && finalErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
            TurboLean.ZygoteWorker.emitZygoteReply stdout finalOk none kgActive true envCacheHit prefixCacheHit importUs prefixUs elabUs finalHbs ptNodes (if finalOk then 1 else 0) finalOut finalMsgs finalErrs usedConsts
        | none =>
          -- Fallback: if prefix failed on its own (e.g. split mid-command or error in prefix), elaborate combined prefix + body from baseEnv
          let prefixCode := decodedPrefix?.getD (TurboLean.ZygoteWorker.decodeHexToString hexPrefix)
          let fn := customFileName?.getD "<zygote-shard>"
          let evalCombined := fun (sc : String) =>
            TurboLean.ZygoteWorker.checkShardWithEnv baseEnv (prefixCode ++ "\n" ++ sc) allowStub false fn none encodedLeanArgs
          if isBatchFission then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
            else
              let (bOk, bElabUs, bHbs, bNodes, bVer, bOut, bMsgs, bErrs, bUsed) ←
                TurboLean.ZygoteWorker.runBatchFissionSubs hexSubs evalCombined
              if !bOk && bErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout bOk none kgActive true envCacheHit false importUs prefixUs bElabUs bHbs bNodes bVer bOut bMsgs bErrs bUsed
          else if isRaceCandidates then
            if hexSubs.isEmpty then
              TurboLean.ZygoteWorker.emitZygoteReply stdout false (some "null") kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
            else
              let (rOk, winIdx, rElabUs, rHbs, rNodes, rVer, rOut, rMsgs, rErrs, rUsed) ←
                TurboLean.ZygoteWorker.runRaceCandidatesSubs hexSubs evalCombined (!prefErrs.isEmpty)
              if !rOk && rErrs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
              TurboLean.ZygoteWorker.emitZygoteReply stdout rOk (some winIdx) kgActive true envCacheHit false importUs prefixUs rElabUs rHbs rNodes rVer rOut rMsgs rErrs rUsed
          else if bodyCode.trimAscii.toString.isEmpty then
            TurboLean.ZygoteWorker.emitZygoteReply stdout false none kgActive true envCacheHit false importUs prefixUs 0 prefHbs 0 0 prefOut prefMsgs prefErrs []
          else
            let prefNewlines := prefixCode.toList.filter (· == '\n') |>.length
            let rest := (bodyCode.drop prefNewlines).toString
            let combined := if prefixCode.endsWith "\n" then prefixCode ++ rest else prefixCode ++ "\n" ++ rest
            let (ok, elabUs, hbs, ptNodes, errs, msgs, capOut, usedConsts) ←
              TurboLean.ZygoteWorker.checkShardWithEnv baseEnv combined allowStub evalMode fn emitOlean? encodedLeanArgs
            if !ok && errs.contains TurboLean.ZygoteWorker.runtimePanicErr then poisoned := true
            TurboLean.ZygoteWorker.emitZygoteReply stdout ok none kgActive true envCacheHit false importUs prefixUs elabUs hbs ptNodes (if ok then 1 else 0) capOut msgs errs usedConsts
    | none =>
      let rawErr := envErr?.getD "importModules failed"
      let formattedErr := match customFileName? with
        | some fn => if evalMode && !rawErr.startsWith fn then s!"{fn}:1:0: error: {rawErr}\n" else rawErr
        | none => rawErr
      TurboLean.ZygoteWorker.emitZygoteReply stdout false none false false false false importUs 0 0 0 0 0 "" [formattedErr] [formattedErr] []
    if boundImports?.isNone && !importsCsv.isEmpty then
      boundImports? := some importsCsv
    try IO.Process.setCurrentDir initCwd catch _ => pure ()
