/-
  Track B0 (spec v4, deliverables 3 + 4): shadow-semantics checker and blocking ratchet.

  Run from `lean/`:
    lake env lean --run ../scripts/check_shadow_semantics.lean [--base REV] [--json-out PATH]
        [--coverage-out PATH] [--self-test] [--bootstrap]

  The checker imports every built module under the inventory `source_roots`, collects every
  constant that belongs to a pinned target module or namespace (`scripts/shadow_inventory.json`),
  and reports each violation identity `(target declaration, forbidden constant, kind)` with
  `kind ∈ {call≤3, call∞, clone}`:

  * `call≤3` / `call∞`: the forbidden constant is reachable from the target in the dependency
    graph whose edges are the constants of each declaration's type, value, `.proj` nodes (structure
    and its constructor), inductive constructors, recursor rules (`RecursorRule.rhs`) and the
    declaration's matcher / equation / `_unsafe_rec` / `match_n` auxiliaries. The graph search is
    a 0-1 BFS (auxiliary edges cost 0 hops), hence cycle safe; hop count ≤ 3 → `call≤3`.
  * `clone`: some constant in the target's dependency closure (the target itself, a helper in ANY
    module / namespace, an `implemented_by` target, an instance, an auxiliary, … — the same graph
    as above, restricted to non-forbidden definitions) has a canonical body equal to that of a
    forbidden evaluator; the hit is attributed to the target, with the path as witness.
    Canonicalization (spec [Q3]): delta-unfold ALL matchers (`Lean.Meta.isMatcher`) and the
    definition's own auxiliaries (`_f`, `_unary`, `_mutual`, `_unsafe_rec`, `match_n`, ...)
    regardless of namespace prefix, beta-reduce, instantiate level params positionally, replace
    self references by a placeholder, erase mdata / binder names / binder infos. Scope:
    verbatim / alpha-equivalent copies only; eta-, let- and arm-reordering evasions are out of
    scope (documented in the PR).

  Forbidden set: every constant `LeanNative.Semantics.eval*` and all its auxiliaries
  (`LeanNative.Semantics.eval*.*`), private or not.

  Ratchet (blocking): the current violation set must be a subset of the allowlist read from
  `git show $BASE:scripts/shadow_allowlist.json`; the working-tree allowlist must itself be a
  subset of the base allowlist (no additions) and must not contain stale entries; the inventory
  may not drop any module / namespace present at base or in the hard-coded minimum below.
  Bootstrap: when the base commit has neither this checker nor an allowlist (only the PR that
  introduces the checker), the base allowlist is taken to be the current violation set, so the
  introducing allowlist must list exactly the existing violations. `--bootstrap` only skips the
  allowlist comparison for local inventory dumps; CI never passes it.
-/
import Lean

open Lean Meta

namespace ShadowCheck

/-! ## Configuration -/

/-- Hard-coded minimum inventory: the JSON file may extend it, never shrink it. -/
def minModules : List Name :=
  [`LeanNative.Backend.Semantics, `LeanNative.IR.LCNF, `TurboLean.ConLeche]
def minNamespaces : List Name := [`LeanMLIR, `LNSym, `ConLeche, `LCNF]
def forbiddenNs : Name := `LeanNative.Semantics
def forbiddenPrefix : String := "eval"
def requiredForbidden : List Name :=
  [`LeanNative.Semantics.evalCode, `LeanNative.Semantics.evalExpr,
   `LeanNative.Semantics.evalBinOp, `LeanNative.Semantics.evalUnaryOp,
   `LeanNative.Semantics.evalScalarExpr]

def inventoryPath : String := "scripts/shadow_inventory.json"
def allowlistPath : String := "scripts/shadow_allowlist.json"
def checkerPath : String := "scripts/check_shadow_semantics.lean"

/-- Self-test fixture namespaces (compiled only in the `ShadowFixtures` lib). -/
def fixtureNamespaces : List Name :=
  [`ShadowFixtureDirect, `ShadowFixtureClone, `ShadowFixtureBitVec, `ShadowFixtureAllowlisted,
   `ShadowFixtureHelperClone]

structure Inventory where
  modules : List Name
  namespaces : List Name
  sourceRoots : List String
  deriving Inhabited

structure Violation where
  target : Name
  forbidden : Name
  kind : String
  hops : Nat := 0
  path : List Name := []
  file : String := ""
  line : Nat := 0
  deriving Inhabited

def Violation.key (v : Violation) : String := s!"{v.target}|{v.forbidden}|{v.kind}"

structure AllowEntry where
  target : String
  forbidden : String
  kind : String
  deriving Inhabited

def AllowEntry.key (a : AllowEntry) : String := s!"{a.target}|{a.forbidden}|{a.kind}"

/-! ## Small utilities -/

def userName (n : Name) : Name := privateToUserName n

def strName (s : String) : Name := s.toName

def jsonStrList (j : Json) (k : String) : Except String (List String) := do
  let arr ← (j.getObjValD k).getArr?
  arr.toList.mapM (·.getStr?)

def parseInventory (s : String) : Except String Inventory := do
  let j ← Json.parse s
  let mods ← jsonStrList j "modules"
  let nss ← jsonStrList j "namespaces"
  let roots ← jsonStrList j "source_roots"
  return { modules := mods.map strName, namespaces := nss.map strName, sourceRoots := roots }

def parseAllowlist (s : String) : Except String (List AllowEntry) := do
  let j ← Json.parse s
  let arr ← (j.getObjValD "entries").getArr?
  arr.toList.mapM fun e => do
    return { target := ← (e.getObjValD "target").getStr?,
             forbidden := ← (e.getObjValD "forbidden").getStr?,
             kind := ← (e.getObjValD "kind").getStr? }

/-- Run `git` in the repository root; `none` if it exits non-zero. -/
def git? (repo : System.FilePath) (args : Array String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "git", args, cwd := some repo }
  return if out.exitCode == 0 then some out.stdout else none

/-- `git show REV:path`. Fails closed if `REV` is not a commit; `none` if the path is absent. -/
def gitShowAt (repo : System.FilePath) (rev path : String) : IO (Option String) := do
  if (← git? repo #["cat-file", "-e", s!"{rev}^\{commit}"]).isNone then
    throw <| IO.userError s!"base revision `{rev}` is not a commit reachable in this clone"
  if (← git? repo #["cat-file", "-e", s!"{rev}:{path}"]).isNone then return none
  git? repo #["show", s!"{rev}:{path}"]

/-! ## Forbidden set and auxiliaries -/

/-- `LeanNative.Semantics.eval*` and every `LeanNative.Semantics.eval*.*` auxiliary. -/
def isForbidden (n : Name) : Bool :=
  let u := userName n
  let rec go : Name → Bool
    | .str p s => (p == forbiddenNs && s.startsWith forbiddenPrefix) || go p
    | .num p _ => go p
    | .anonymous => false
  go u

/-- The top-level forbidden evaluator owning a forbidden constant (`evalBinOp.match_3 ↦ evalBinOp`). -/
def forbiddenOwner (n : Name) : Name :=
  let rec go : Name → Name
    | n@(.str p s) => if p == forbiddenNs && s.startsWith forbiddenPrefix then n else go p
    | .num p _ => go p
    | .anonymous => .anonymous
  go (userName n)

/-- Is `n` an implementation detail of some declaration (matcher, equation lemma, `_unsafe_rec`, …)? -/
def isAuxName (n : Name) : Bool :=
  let u := userName n
  u.isInternalDetail ||
    (match u with
     | .str _ s => s == "eq_def" || s.startsWith "eq_" || s == "_unsafe_rec" || s.startsWith "match_"
     | _ => false)

/-- The user-facing declaration that owns an auxiliary (`LCNF.evalLetValue.match_3 ↦ LCNF.evalLetValue`). -/
partial def ownerDecl (env : Environment) (n : Name) : Name :=
  if !isAuxName n then n
  else match n with
    | .str p _ | .num p _ =>
      if p.isAnonymous then n
      else if env.contains p && !isAuxName p then p else ownerDecl env p
    | .anonymous => n

/-- Auxiliary constants attached to `c` that must be traversed with `c` (cost 0). -/
def auxiliariesOf (env : Environment) (c : Name) : List Name := Id.run do
  let mut out := []
  for s in ["_unsafe_rec", "eq_def", "_unary", "_binary", "_mutual"] do
    let n := c ++ strName s
    if env.contains n then out := n :: out
  let mut i := 1
  while i ≤ 64 do
    let n := Name.str c s!"eq_{i}"
    if env.contains n then out := n :: out; i := i + 1 else i := 65
  if let some impl := Compiler.getImplementedBy? env c then out := impl :: out
  return out

/-! ## Dependency edges -/

/-- Constants referenced by `e`, including `.proj` structure names and their constructors. -/
def exprRefs (env : Environment) (e : Expr) : IO (Array Name) := do
  let acc ← IO.mkRef (#[] : Array Name)
  e.forEach' fun sub => do
    match sub with
    | .const n _ => acc.modify (·.push n)
    | .proj s _ _ =>
      acc.modify (·.push s)
      if isStructure env s then acc.modify (·.push (getStructureCtor env s).name)
    | _ => pure ()
    return true
  return (← acc.get)

def constRefs (env : Environment) (c : Name) : IO (Array Name) := do
  let some ci := env.find? c | return #[]
  let mut out ← exprRefs env ci.type
  match ci with
  | .defnInfo v => out := out ++ (← exprRefs env v.value)
  | .thmInfo v => out := out ++ (← exprRefs env v.value)
  | .opaqueInfo v => out := out ++ (← exprRefs env v.value)
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for r in v.rules do out := out ++ (← exprRefs env r.rhs)
  | _ => pure ()
  return out ++ (auxiliariesOf env c).toArray

/-! ## Graph search (reverse 0-1 BFS, cycle safe) -/

/-- Edge `c → r` costs 0 hops when `r` is an auxiliary of the same declaration as `c`
    (its matchers / equations / `_unsafe_rec` / `match_n` / `implemented_by` target), else 1. -/
def edgeCost (env : Environment) (c r : Name) : Nat :=
  if isAuxName r && userName (ownerDecl env r) == userName (ownerDecl env c) then 0 else 1

/-- Forward reference graph over every constant of `relevantMods` (modules that transitively
    import the evaluator; no other module can mention a forbidden constant), built once. -/
def buildGraph (env : Environment) (relevantMods : Std.HashSet Nat) :
    IO (Std.HashMap Name (Array (Name × Nat))) := do
  let mut rev : Std.HashMap Name (Array (Name × Nat)) := {}
  for (c, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? c | continue
    unless relevantMods.contains i.toNat do continue
    if isForbidden c then continue   -- forbidden constants are sinks
    for r in (← constRefs env c) do
      if r == c then continue
      rev := rev.insert r ((rev[r]?.getD #[]).push (c, edgeCost env c r))
  return rev

structure Hit where
  forbidden : Name
  hops : Nat
  path : List Name

/-- For each group `(F, sources)`, minimal hops from every constant to one of `sources`, never
    passing through a forbidden constant (forbidden constants are sinks). Call groups use `F`'s
    own constants as sources; clone groups use the constants whose canonical body equals `F`'s, so
    a clone ANYWHERE in a target's dependency closure (helper in an unpinned module / namespace,
    `implemented_by` target, instance, auxiliary, …) is attributed to the target.
    Returns `constant ↦ hits` (a source itself is a hit at distance 0). -/
def reverseSearch (rev : Std.HashMap Name (Array (Name × Nat)))
    (groups : Array (Name × Array Name)) : Std.HashMap Name (Array Hit) := Id.run do
  let mut out : Std.HashMap Name (Array Hit) := {}
  for (f, srcs) in groups do
    let mut dist : Std.HashMap Name Nat := {}
    let mut next : Std.HashMap Name Name := {}   -- successor toward `f`
    for s in srcs do dist := dist.insert s 0
    let mut front := srcs
    let mut d := 0
    while !front.isEmpty do
      let mut layer := front
      let mut idx := 0
      let mut nxt : Array Name := #[]
      while idx < layer.size do
        let v := layer[idx]!
        idx := idx + 1
        if dist[v]? != some d then continue
        for (u, w) in rev[v]?.getD #[] do
          if isForbidden u then continue
          let nd := d + w
          if let some old := dist[u]? then if old ≤ nd then continue
          dist := dist.insert u nd
          next := next.insert u v
          if w == 0 then layer := layer.push u else nxt := nxt.push u
      front := nxt
      d := d + 1
    for (u, h) in dist.toList do
      if isForbidden u then continue
      let mut path := [u]
      let mut cur := u
      let mut guard := 0
      while guard < 10000 do
        let some n := next[cur]? | break
        path := path ++ [n]
        cur := n
        guard := guard + 1
      out := out.insert u ((out[u]?.getD #[]).push { forbidden := userName f, hops := h, path })
  return out

/-! ## Clone canonicalization -/

def selfPlaceholder : Name := `_shadow_self

/-- Unfold matchers and local auxiliaries of `root`, replace self references. -/
partial def unfoldAux (env : Environment) (root : Name) (fuel : Nat) (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub with
    | .const n us =>
      let un := userName n
      if un == userName root then some (.const selfPlaceholder [])
      else if fuel == 0 then none
      else
        let isLocal := (userName root).isPrefixOf un && isAuxName n
        -- `_sparseCasesOn_k` are matcher-like casesOn wrappers that Lean SHARES across
        -- declarations (e.g. `evalUnaryOp` reuses `evalBinOp._sparseCasesOn_1`), so unfold them
        -- regardless of owner, like matchers.
        let isSparse := match un with
          | .str _ s => s.startsWith "_sparseCasesOn"
          | _ => false
        if isMatcherCore env n || isLocal || isSparse then
          match env.find? n with
          | some ci@(.defnInfo _) =>
            some (unfoldAux env root (fuel - 1) (ci.instantiateValueLevelParams! us))
          | _ => none
        else none
    | _ => none

/-- Erase mdata, binder names and binder infos. -/
partial def eraseNames (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub with
    | .mdata _ b => some (eraseNames b)
    | .lam _ t b _ => some (.lam .anonymous (eraseNames t) (eraseNames b) .default)
    | .forallE _ t b _ => some (.forallE .anonymous (eraseNames t) (eraseNames b) .default)
    | .letE _ t v b _ => some (.letE .anonymous (eraseNames t) (eraseNames v) (eraseNames b) false)
    | _ => none

def canonical (env : Environment) (c : Name) : CoreM (Option Expr) := do
  let some ci := env.find? c | return none
  let .defnInfo v := ci | return none
  let lvls := (List.range v.levelParams.length).map fun i => Level.param (strName s!"u_{i}")
  let body := v.value.instantiateLevelParams v.levelParams lvls
  let body := unfoldAux env c 64 body
  let body ← Core.betaReduce body
  return some (eraseNames body)


/-! ## Target collection -/

/-- Module names of every `.lean` file under `lean/<root>` (plus `lean/<root>.lean`). -/
def discoverModules (leanDir : System.FilePath) (roots : List String) : IO (Array Name) := do
  let mut out := #[]
  for r in roots do
    if ← (leanDir / s!"{r}.lean").pathExists then out := out.push (strName r)
    let dir := leanDir / r
    if ← dir.isDir then
      for f in ← dir.walkDir do
        if f.extension == some "lean" then
          let rel := (f.toString.drop (leanDir.toString.length + 1)).toString
          let modStr := ((rel.dropEnd 5).toString).replace "/" "."
          out := out.push (strName modStr)
  return out.qsort (·.toString < ·.toString)

def inNamespace (nss : List Name) (n : Name) : Bool :=
  nss.any (·.isPrefixOf (userName n))

/-- Every non-auxiliary constant in a pinned module or under a pinned namespace (outside the
    forbidden evaluator itself). Auxiliaries are reached through their owner. -/
def collectTargets (env : Environment) (inv : Inventory) : Array Name := Id.run do
  let modIdxs : Std.HashSet Nat := inv.modules.foldl (init := {}) fun s m =>
    match env.getModuleIdx? m with | some i => s.insert i.toNat | none => s
  let mut out := #[]
  for (n, _) in env.constants.toList do
    if isForbidden n || isAuxName n then continue
    let inMod := match env.getModuleIdxFor? n with
      | some i => modIdxs.contains i.toNat
      | none => false
    if inMod || inNamespace inv.namespaces n then out := out.push n
  return out.qsort (·.toString < ·.toString)

/-- Module indices whose transitive imports include one of `anchors` (or that are an anchor).
    Every constant that can reach a source constant lives in a module importing the source's
    module, so restricting the graph to these modules loses no path. -/
def importersOf (env : Environment) (anchors : Std.HashSet Name) : Std.HashSet Nat := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut rel : Std.HashSet Name := {}
  let mut idx : Std.HashSet Nat := {}
  -- moduleNames is topologically ordered (dependencies first)
  for i in [0:names.size] do
    let m := names[i]!
    let deps := data[i]!.imports.map (·.module)
    if anchors.contains m || deps.any rel.contains then
      rel := rel.insert m
      idx := idx.insert i
  return idx

def constsOf (e : Expr) : Std.HashSet Name :=
  e.foldConsts {} fun c s => s.insert c

/-- Clone anchor of a forbidden evaluator: the topologically LAST module defining a constant of
    its canonical body. A verbatim / alpha-equivalent copy has the same canonical body, so it
    mentions that constant and its module transitively imports the anchor. -/
def cloneAnchor (env : Environment) (canon : Expr) : Option Name := Id.run do
  let mut best : Option Nat := none
  for c in constsOf canon do
    if let some i := env.getModuleIdxFor? c then
      if best.all (· < i.toNat) then best := some i.toNat
  return best.map (env.header.moduleNames[·]!)

def declLoc (env : Environment) (leanDir : System.FilePath) (n : Name) : IO (String × Nat) := do
  let owner := ownerDecl env n
  let file := match env.getModuleIdxFor? owner with
    | some i => s!"lean/{(env.header.moduleNames[i.toNat]!).toString.replace "." "/"}.lean"
    | none => ""
  let _ := leanDir
  let ranges := declRangeExt.find? (level := .server) env owner <|>
    declRangeExt.find? (level := .exported) env owner
  return (file, ranges.map (·.selectionRange.pos.line) |>.getD 0)

/-! ## Analysis -/

structure Report where
  targets : Array Name
  targetLocs : Array (Name × String × Nat) := #[]
  violations : Array Violation
  forbidden : Array Name
  deriving Inhabited

def stage (msg : String) : IO Unit := do
  IO.eprintln s!"[shadow-semantics +{← IO.monoMsNow}ms] {msg}"
  (← IO.getStderr).flush

def analyze (env : Environment) (leanDir : System.FilePath) (inv : Inventory) : IO Report := do
  stage "collect targets"
  let targets := collectTargets env inv
  stage s!"{targets.size} targets"
  let forbidden := (env.constants.toList.filterMap fun (n, _) =>
    if isForbidden n then some n else none).toArray
  let forbiddenEvals := forbidden.filter fun n => !isAuxName n && forbiddenOwner n == userName n
  -- canonical forms of forbidden evaluator bodies (NOT of shared utilities)
  let ctx : Core.Context := { fileName := "<shadow-check>", fileMap := default,
                              maxHeartbeats := 0, maxRecDepth := 100000 }
  let st : Core.State := { env }
  let canonOf (c : Name) : IO (Option Expr) := (canonical env c).toIO' ctx st
  let mut evalCanon : Array (Name × Expr) := #[]
  let mut anchors : Std.HashSet Name := ({} : Std.HashSet Name).insert `LeanNative.Semantics.Eval
  for f in forbiddenEvals do
    if let some e ← canonOf f then
      evalCanon := evalCanon.push (f, e)
      if let some a := cloneAnchor env e then anchors := anchors.insert a
  let relIdx := importersOf env anchors
  -- Clone sources: EVERY non-forbidden definition of the relevant modules (not only targets)
  -- whose canonical body equals a forbidden evaluator's. They are then searched for like the
  -- evaluator itself, so a clone hidden in a helper outside the pinned modules / namespaces, an
  -- `implemented_by` target, an instance or an auxiliary is attributed to every target reaching it.
  stage s!"clone canonicalization over {relIdx.size} relevant modules"
  let evalHashes : Std.HashSet UInt64 := evalCanon.foldl (·.insert ·.2.hash) {}
  let mut cloneSrcs : Std.HashMap Name (Array Name) := {}
  for (c, ci) in env.constants.toList do
    let .defnInfo _ := ci | continue
    if isForbidden c then continue
    let some i := env.getModuleIdxFor? c | continue
    unless relIdx.contains i.toNat do continue
    let some e ← canonOf c | continue
    unless evalHashes.contains e.hash do continue
    for (f, fe) in evalCanon do
      if e == fe then cloneSrcs := cloneSrcs.insert f ((cloneSrcs[f]?.getD #[]).push c)
  stage s!"build graph; clone sources: {cloneSrcs.toList.map fun (f, cs) => (f, cs.size)}"
  let rev ← buildGraph env relIdx
  stage s!"graph: {rev.size} referenced nodes; reverse search"
  let callGroups := forbiddenEvals.map fun f => (f, forbidden.filter (forbiddenOwner · == userName f))
  let callHits := reverseSearch rev callGroups
  let cloneHits := reverseSearch rev (cloneSrcs.toArray)
  stage s!"search done ({callHits.size} call-reaching, {cloneHits.size} clone-reaching constants)"
  let mut vs : Array Violation := #[]
  let mut targetLocs := #[]
  for t in targets do
    let (file, line) ← declLoc env leanDir t
    targetLocs := targetLocs.push (userName t, file, line)
    -- a target's own auxiliaries are part of it (0-cost edges), so fold their hits in too
    for h in callHits[t]?.getD #[] do
      let kind := if h.hops ≤ 3 then "call≤3" else "call∞"
      vs := vs.push { target := userName t, forbidden := h.forbidden, kind,
                      hops := h.hops, path := h.path.map userName, file, line }
    for h in cloneHits[t]?.getD #[] do
      vs := vs.push { target := userName t, forbidden := h.forbidden, kind := "clone",
                      hops := h.hops, path := h.path.map userName, file, line }
  stage "attribution done"
  -- dedupe by identity, keep the shortest witness
  let mut best : Std.HashMap String Violation := {}
  for v in vs do
    match best[v.key]? with
    | some old => if v.hops < old.hops then best := best.insert v.key v
    | none => best := best.insert v.key v
  let out := best.toArray.map (·.2) |>.qsort (·.key < ·.key)
  return { targets, targetLocs, violations := out, forbidden := forbiddenEvals }

/-- Rebuild a name from fresh heap objects (no pointers into an `.olean` region). -/
def freshName : Name → Name
  | .str p s => .str (freshName p) (String.ofList s.toList)
  | .num p k => .num (freshName p) k
  | .anonymous => .anonymous

def freshStr (s : String) : String := String.ofList s.toList

/-- Deep copy, so the report survives `Environment.freeRegions`. -/
def Report.fresh (r : Report) : Report :=
  { targets := r.targets.map freshName,
    targetLocs := r.targetLocs.map fun (n, f, l) => (freshName n, freshStr f, l),
    violations := r.violations.map fun v =>
      { v with target := freshName v.target, forbidden := freshName v.forbidden,
               kind := freshStr v.kind, path := v.path.map freshName, file := freshStr v.file },
    forbidden := r.forbidden.map freshName }

/-- Union of reports from several environments (dedupe by identity / name). -/
def Report.merge (a b : Report) : Report := Id.run do
  let mut vs := a.violations
  for v in b.violations do
    unless vs.any (·.key == v.key) do vs := vs.push v
  let mut ts := a.targetLocs
  for t in b.targetLocs do
    unless ts.any (·.1 == t.1) do ts := ts.push t
  let mut fs := a.forbidden
  for f in b.forbidden do
    unless fs.contains f do fs := fs.push f
  return { targets := ts.map (·.1), targetLocs := ts.qsort (·.1.toString < ·.1.toString),
           violations := vs.qsort (·.key < ·.key), forbidden := fs }

/-! ## Output -/

def Violation.toJson (v : Violation) : Json :=
  Json.mkObj [("target", toString v.target), ("forbidden", toString v.forbidden),
    ("kind", v.kind), ("hops", v.hops), ("file", v.file), ("line", v.line),
    ("path", Json.arr (v.path.toArray.map (Json.str ∘ toString)))]

def printTable (vs : Array Violation) : IO Unit := do
  for v in vs do
    let witness := " → ".intercalate (v.path.map toString) ++
      (if v.kind == "clone" then " ≅ (canonical body equal)" else "")
    IO.println s!"  {v.kind}\t{v.target}\t→ {v.forbidden}\t{v.file}:{v.line}\t{witness}"

/-! ## Ratchet -/

def checkRatchet (repo : System.FilePath) (base : String) (inv : Inventory)
    (vs : Array Violation) : IO (Array String) := do
  let mut errs := #[]
  let curS ← IO.FS.readFile (repo / allowlistPath)
  let cur ← IO.ofExcept (parseAllowlist curS)
  -- Bootstrap is detected, never requested: it applies only when the base commit predates the
  -- checker itself (no checker AND no allowlist at base). Then the base allowlist is taken to be
  -- exactly the current violation set, i.e. the introducing commit must allowlist precisely what
  -- exists — no more, no less. Once the checker is on the base branch this path is unreachable.
  let baseA ← match ← gitShowAt repo base allowlistPath with
    | some baseS => IO.ofExcept (parseAllowlist baseS)
    | none =>
      if (← gitShowAt repo base checkerPath).isSome then
        return errs.push s!"base {base} has the checker but no {allowlistPath}"
      IO.println s!"[shadow-semantics] bootstrap: base {base} predates the checker; allowlist must equal the current violation set"
      pure (vs.toList.map fun v =>
        ({ target := toString v.target, forbidden := toString v.forbidden, kind := v.kind } : AllowEntry))
  let baseKeys : Std.HashSet String := baseA.foldl (·.insert ·.key) {}
  for a in cur do
    unless baseKeys.contains a.key do
      errs := errs.push s!"allowlist ADDS entry not in base {base}: {a.key}"
  for v in vs do
    unless baseKeys.contains v.key do
      errs := errs.push s!"NEW violation not in base allowlist: {v.key} ({v.file}:{v.line})"
  let vKeys : Std.HashSet String := vs.foldl (·.insert ·.key) {}
  for a in cur do
    unless vKeys.contains a.key do
      errs := errs.push s!"stale allowlist entry (violation gone; remove it): {a.key}"
  -- inventory may not shrink relative to base
  if let some baseInvS ← gitShowAt repo base inventoryPath then
    let bi ← IO.ofExcept (parseInventory baseInvS)
    for m in bi.modules do
      unless inv.modules.contains m do errs := errs.push s!"inventory drops base module {m}"
    for n in bi.namespaces do
      unless inv.namespaces.contains n do errs := errs.push s!"inventory drops base namespace {n}"
    for r in bi.sourceRoots do
      unless inv.sourceRoots.contains r do errs := errs.push s!"inventory drops base source root {r}"
  return errs

/-! ## Self-test -/

def selfTest (env : Environment) (leanDir : System.FilePath) : IO (Array String) := do
  let inv : Inventory := { modules := [], namespaces := fixtureNamespaces, sourceRoots := [] }
  let r ← analyze env leanDir inv
  IO.println s!"[self-test] {r.targets.size} fixture targets, {r.violations.size} violations:"
  printTable r.violations
  let find (t : Name) (f : Name) (k : String) : Bool :=
    r.violations.any fun v => v.target == t && v.forbidden == f && v.kind == k
  let mut errs := #[]
  -- (1) direct call → fail
  unless find `ShadowFixtureDirect.denote `LeanNative.Semantics.evalBinOp "call≤3" do
    errs := errs.push "fixture direct-call: expected ShadowFixtureDirect.denote → evalBinOp (call≤3)"
  -- (2) verbatim clone in a file importing LeanNative.Semantics.Eval → fail
  unless find `ShadowFixtureClone.evalBinOp `LeanNative.Semantics.evalBinOp "clone" do
    errs := errs.push "fixture verbatim-clone: expected ShadowFixtureClone.evalBinOp ≅ evalBinOp (clone)"
  -- (2b) clone in an un-inventoried helper module / namespace, reached from a target → fail
  unless find `ShadowFixtureHelperClone.denote `LeanNative.Semantics.evalUnaryOp "clone" do
    errs := errs.push "fixture helper-clone: expected ShadowFixtureHelperClone.denote → UnrelatedUtil.unaryCopy ≅ evalUnaryOp (clone)"
  if r.violations.any (fun v => (`UnrelatedUtil).isPrefixOf v.target) then
    errs := errs.push "fixture helper-clone: un-inventoried helper must not itself be a target"
  -- (3) BitVec-only namespace → pass
  if r.violations.any (fun v => (`ShadowFixtureBitVec).isPrefixOf v.target) then
    errs := errs.push "fixture bitvec-only: expected no violation in ShadowFixtureBitVec"
  unless r.targets.any (fun t => (`ShadowFixtureBitVec).isPrefixOf (userName t)) do
    errs := errs.push "fixture bitvec-only: namespace not inventoried (vacuous pass)"
  -- (4) second violation in an allowlisted namespace → ratchet fails
  let allow : Std.HashSet String :=
    ({} : Std.HashSet String).insert
      s!"ShadowFixtureAllowlisted.first|LeanNative.Semantics.evalBinOp|call≤3"
  let fixtureVs := r.violations.filter fun v => (`ShadowFixtureAllowlisted).isPrefixOf v.target
  let newVs := fixtureVs.filter fun v => !allow.contains v.key
  unless fixtureVs.any (·.key == s!"ShadowFixtureAllowlisted.first|LeanNative.Semantics.evalBinOp|call≤3") do
    errs := errs.push "fixture allowlisted-second: allowlisted `first` violation not detected"
  unless newVs.any (fun v => v.target == `ShadowFixtureAllowlisted.second &&
      v.forbidden == `LeanNative.Semantics.evalUnaryOp && v.kind == "call≤3") do
    errs := errs.push "fixture allowlisted-second: ratchet did not flag `second` (2 hops) as new"
  -- ratchet subset logic on synthetic allowlists
  let fakeBase : List AllowEntry := [{ target := "A", forbidden := "B", kind := "clone" }]
  let fakeCur : List AllowEntry := fakeBase ++ [{ target := "C", forbidden := "D", kind := "call∞" }]
  let baseKeys : Std.HashSet String := fakeBase.foldl (·.insert ·.key) {}
  unless fakeCur.any (fun a => !baseKeys.contains a.key) do
    errs := errs.push "ratchet: allowlist addition not detected"
  -- forbidden set sanity: auxiliaries are forbidden
  unless isForbidden `LeanNative.Semantics.evalBinOp.match_1 && !isForbidden `LeanNative.Semantics.Val.toU256? do
    errs := errs.push "forbidden-set predicate wrong"
  IO.println s!"[self-test] {if errs.isEmpty then "PASS" else "FAIL"}: direct-call→fail, verbatim-clone→fail, bitvec-only→pass, allowlisted-second→fail"
  return errs

/-! ## Driver -/

structure Args where
  base : Option String := none
  jsonOut : Option String := none
  coverageOut : Option String := none
  selfTest : Bool := false
  bootstrap : Bool := false

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--base" :: r :: rest, a => parseArgs rest { a with base := some r }
  | "--json-out" :: p :: rest, a => parseArgs rest { a with jsonOut := some p }
  | "--coverage-out" :: p :: rest, a => parseArgs rest { a with coverageOut := some p }
  | "--self-test" :: rest, a => parseArgs rest { a with selfTest := true }
  | "--bootstrap" :: rest, a => parseArgs rest { a with bootstrap := true }
  | x :: _, _ => .error s!"unknown argument {x}"

unsafe def run (args : Args) : IO UInt32 := do
  let leanDir ← IO.currentDir
  let repo := leanDir / ".."
  unless ← (leanDir / "lakefile.lean").pathExists do
    throw <| IO.userError "run from the `lean/` directory: cd lean && lake env lean --run ../scripts/check_shadow_semantics.lean"
  let inv ← IO.ofExcept (parseInventory (← IO.FS.readFile (repo / inventoryPath)))
  let mut errs : Array String := #[]
  for m in minModules do
    unless inv.modules.contains m do errs := errs.push s!"inventory missing pinned module {m}"
  for n in minNamespaces do
    unless inv.namespaces.contains n do errs := errs.push s!"inventory missing pinned namespace {n}"
  let mut modsArr ← discoverModules leanDir inv.sourceRoots
  for m in inv.modules do
    unless modsArr.contains m do errs := errs.push s!"pinned module {m} has no source file"
  if args.selfTest then modsArr := modsArr.push `ShadowFixtures
  initSearchPath (← findSysroot)
  -- Source files that no Lake library builds (e.g. `TurboLean.lean` under a `.submodules` glob)
  -- have no `.olean`; they are not part of any built artifact. Skip them loudly; a pinned module
  -- without an `.olean` is a hard failure.
  let mut built := #[]
  for m in modsArr do
    let ok ← try pure (← (← findOLean m).pathExists) catch _ => pure false
    if ok then built := built.push m
    else if inv.modules.contains m then errs := errs.push s!"pinned module {m} is not built"
    else IO.println s!"[shadow-semantics] note: {m} has no .olean (not in any Lake library); skipped"
  modsArr := built
  enableInitializersExecution
  -- Executable root modules each define a top-level `main`, so they cannot share one
  -- environment. Analyze the library modules together, then each exe root on top of them.
  let mut mainMods := #[]
  for m in modsArr do
    let src := leanDir / s!"{m.toString.replace "." "/"}.lean"
    if ← src.pathExists then
      let txt ← IO.FS.readFile src
      if (txt.splitOn "\n").any (fun l => ["def main", "unsafe def main", "partial def main"].any (fun (pre : String) => l.startsWith pre)) then
        mainMods := mainMods.push m
  let libMods := modsArr.filter (!mainMods.contains ·)
  let envSets : Array (Array Name) := #[libMods] ++ mainMods.map (libMods.push ·)
  let mut report? : Option Report := none
  let mut seenMods : Std.HashSet Name := {}
  let mut seenNs : Std.HashSet Name := {}
  let mut seenForbidden : Std.HashSet Name := {}
  let mut first := true
  for mods in envSets do
    let imports := mods.map fun m => ({ module := m } : Import)
    stage s!"import env #{mods.size} (last: {mods.back?})"
    -- `loadExts := false`: do not run user `initialize` blocks of analyzed modules (some spawn
    -- processes / block). Built-in extensions (decl ranges, matchers, `implemented_by`) still load.
    let env ← importModules imports {} (loadExts := false)
    for m in inv.modules do
      if (env.getModuleIdx? m).isSome then seenMods := seenMods.insert m
    for n in inv.namespaces do
      if env.constants.toList.any (fun (c, _) => n.isPrefixOf (userName c)) then seenNs := seenNs.insert n
    for f in requiredForbidden do
      if env.contains f then seenForbidden := seenForbidden.insert f
    if first && args.selfTest then
      errs := errs ++ (← selfTest env leanDir).map freshStr
    first := false
    stage "imported; pinned checks"
    let r := (← analyze env leanDir inv).fresh
    report? := some (match report? with | some a => a.merge r | none => r)
    -- Release the mmapped .olean regions before the next import: repeated imports in one process
    -- otherwise stall (observed on the 4th environment). `r` holds only names/strings.
    env.freeRegions
  for m in inv.modules do
    unless seenMods.contains m do errs := errs.push s!"pinned module {m} not imported"
  for n in inv.namespaces do
    unless seenNs.contains n do errs := errs.push s!"pinned namespace {n} has no declarations (missing/unimported)"
  for f in requiredForbidden do
    unless seenForbidden.contains f do errs := errs.push s!"forbidden evaluator {f} missing from environment"
  stage "all environments analyzed"
  let r := report?.get!
  IO.println s!"[shadow-semantics] {modsArr.size} modules imported ({envSets.size} environments: libraries + {mainMods.size} exe roots), {r.targets.size} target declarations, {r.forbidden.size} forbidden evaluators"
  IO.println s!"[shadow-semantics] {r.violations.size} violations:"
  printTable r.violations
  if let some p := args.jsonOut then
    IO.FS.writeFile p ((Json.mkObj [("violations", Json.arr (r.violations.map Violation.toJson)),
      ("forbidden_evaluators", Json.arr (r.forbidden.map (Json.str ∘ toString)))]).pretty ++ "\n")
  if let some p := args.coverageOut then
    let lines := r.targetLocs.map fun (t, f, l) => s!"{t}\t{f}:{l}"
    IO.FS.writeFile p ("\n".intercalate lines.toList ++ "\n")
  match args.base with
  | some b => errs := errs ++ (← checkRatchet repo b inv r.violations)
  | none =>
    if !args.bootstrap then
      -- without a base, compare against the working-tree allowlist (local developer mode)
      let cur ← IO.ofExcept (parseAllowlist (← IO.FS.readFile (repo / allowlistPath)))
      let keys : Std.HashSet String := cur.foldl (·.insert ·.key) {}
      for v in r.violations do
        unless keys.contains v.key do errs := errs.push s!"violation not in allowlist: {v.key} ({v.file}:{v.line})"
      let vKeys : Std.HashSet String := r.violations.foldl (·.insert ·.key) {}
      for a in cur do
        unless vKeys.contains a.key do errs := errs.push s!"stale allowlist entry: {a.key}"
  if errs.isEmpty then
    IO.println "[shadow-semantics] PASS"
    return 0
  IO.eprintln s!"[shadow-semantics] FAIL ({errs.size}):"
  for e in errs do IO.eprintln s!"  - {e}"
  return 1

end ShadowCheck

unsafe def main (argv : List String) : IO UInt32 := do
  match ShadowCheck.parseArgs argv {} with
  | .error e => IO.eprintln e; return 2
  | .ok a => ShadowCheck.run a
