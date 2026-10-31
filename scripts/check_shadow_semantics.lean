/-
  Track B0 (spec v4, deliverables 3 + 4): shadow-semantics checker and ratchet.

  Run from `lean/`:
    lake env lean --run ../scripts/check_shadow_semantics.lean [--base REV] [--json-out PATH]
        [--coverage-out PATH] [--self-test] [--bootstrap]

  The checker imports every built module under the inventory `source_roots` (compiling any
  standalone `<root>.lean` file excluded by Lake globs into a scratch `.olean`), collects every
  constant that belongs to a pinned target module or namespace (`scripts/shadow_inventory.json`)
  or opens a banned local shadow namespace inside `lean/LeanNative/Proofs/`, and reports each
  violation identity `(target declaration, forbidden constant, kind)` with
  `kind ∈ {call≤3, call∞, clone, shadow-origin}`:

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
  * `shadow-origin`: any declaration under a pinned shadow namespace (`ConLeche`, `LCNF`,
    `LeanMLIR`, `LNSym`) defined outside its pinned grandfather module (`TurboLean.ConLeche`,
    `LeanNative.IR.LCNF`, `LeanNative.Backend.Semantics`), OR any declaration inside
    `LeanNative.Proofs.*` that defines a local shadow/stub namespace (`ConLeche`, `LCNF`,
    `LeanMLIR`, `LNSym`) anywhere in its name (even if it never mentions `LeanNative.Semantics.eval*`,
    such as a toy `CICValid` equality stub or an empty-list `parseOleanShard`). Existing stand-in
    declarations live in the pinned grandfather modules and are subject to the remove-only ratchet.

  Forbidden set: every constant `LeanNative.Semantics.eval*` and all its auxiliaries
  (`LeanNative.Semantics.eval*.*`), private or not.

  Ratchet (fails the CI job; merge-blocking only once `main` requires that check — see
  docs/SHADOW_SEMANTICS.md "Enforcement"): the current violation set must be a subset of the allowlist read from
  `git show $BASE:scripts/shadow_allowlist.json`; the working-tree allowlist must itself be a
  subset of the base allowlist (no additions) AND equal the current violation set (no missing,
  no stale entries); the inventory may not drop any module / namespace present at base or in the
  hard-coded minimum below. Bootstrap: when the base commit has neither this checker nor an
  allowlist (only the PR that introduces the checker), the base allowlist is taken to be the
  current violation set; the equality check then forces the introducing allowlist to list exactly
  the existing violations (an empty allowlist fails). `--bootstrap` only skips the allowlist
  comparison for local inventory dumps; CI never passes it.
-/
import Lean

open Lean Meta

namespace ShadowCheck

/-! ## Configuration -/

/-- Hard-coded minimum inventory: the JSON file may extend it, never shrink it. -/
def minModules : List Name :=
  [`LeanNative.Backend.Semantics, `LeanNative.IR.LCNF, `TurboLean.ConLeche]
def minNamespaces : List Name := [`LeanMLIR, `LNSym, `ConLeche, `LCNF]
def minNamespaceOwners : List (Name × List Name) :=
  [(`LeanMLIR, [`LeanNative.Backend.Semantics]),
   (`LNSym, [`LeanNative.Backend.Semantics]),
   (`ConLeche, [`TurboLean.ConLeche]),
   (`LCNF, [`LeanNative.IR.LCNF])]
def minProofPrefixes : List Name := [`LeanNative.Proofs]
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
   `ShadowFixtureHelperClone, `ShadowFixtureTraversal]

def fixtureProofPrefix : Name := `ShadowFixtureOrigin

structure Inventory where
  modules : List Name
  namespaces : List Name
  sourceRoots : List String
  namespaceOwners : List (Name × List Name) := minNamespaceOwners
  proofPrefixes : List Name := minProofPrefixes
  bannedShadowNames : List Name := minNamespaces
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
  let owners ← match j.getObjValD "namespace_owners" with
    | .null => pure minNamespaceOwners
    | oj => do
      let obj ← oj.getObj?
      obj.toList.mapM fun (k, v) => do
        let arr ← v.getArr?
        let ms ← arr.toList.mapM (·.getStr?)
        pure (strName k, ms.map strName)
  let pfx ← match j.getObjValD "proof_module_prefixes" with
    | .null => pure minProofPrefixes
    | pj => do
      let arr ← pj.getArr?
      let ps ← arr.toList.mapM (·.getStr?)
      pure (ps.map strName)
  return { modules := mods.map strName, namespaces := nss.map strName, sourceRoots := roots,
           namespaceOwners := owners, proofPrefixes := pfx,
           bannedShadowNames := minNamespaces ++ (nss.map strName).filter (!minNamespaces.contains ·) }

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

/-- Is `n` an implementation detail of some declaration (matcher, splitter, equation lemma, `_unsafe_rec`, …)? -/
def isAuxName (n : Name) : Bool :=
  let u := userName n
  u.isInternalDetail ||
    (match u with
     | .str (.str _ pm) "splitter" => pm.startsWith "match_"
     | .str _ s =>
       s == "eq_def" || s.startsWith "eq_" || s == "_unsafe_rec" ||
       s.startsWith "match_" || s == "congr_simp"
     | _ => false)

/-- The user-facing declaration that owns an auxiliary (`LCNF.evalLetValue.match_3 ↦ LCNF.evalLetValue`),
    resolving `_private.<Mod>.0.<Decl>.match_k` back to public `<Decl>` when `<Decl>` is in `env`. -/
partial def ownerDecl (env : Environment) (n : Name) : Name :=
  let resolve (c : Name) : Name :=
    if env.contains c then c else if env.contains (userName c) then userName c else c
  if !isAuxName n then resolve n
  else match n with
    | .str p _ | .num p _ =>
      if p.isAnonymous then resolve n
      else
        let rp := resolve p
        if env.contains rp && !isAuxName rp then rp else ownerDecl env p
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
    -- constants of no module exist only when added in memory (self-test fixtures); keep them
    if let some i := env.getModuleIdxFor? c then
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

/-- Namespace prefix of a user-facing constant (`A.B.foo ↦ A.B`, `foo ↦ anonymous`). -/
def nameParent : Name → Name
  | .str p _ | .num p _ => p
  | .anonymous => .anonymous

/-- String segments of a `Name`. -/
def nameSegments : Name → List String
  | .str p s => nameSegments p ++ [s]
  | .num p k => nameSegments p ++ [toString k]
  | .anonymous => []

/-- True if `segs` occurs as a contiguous sub-list of `haystack`. -/
partial def hasContiguousSublist (segs haystack : List String) : Bool :=
  !segs.isEmpty && (segs.isPrefixOf haystack ||
    match haystack with | [] => false | _ :: tl => hasContiguousSublist segs tl)

/-- Check whether constant `n` defined in module `modName` opens a banned shadow/stub namespace:
    1. `n` begins with a pinned shadow namespace `ns` whose `namespaceOwners` does not allow `modName`.
    2. `modName` is under `inv.proofPrefixes` (e.g. `LeanNative.Proofs.*`) and `n`'s namespace
       hierarchy contains any `inv.bannedShadowNames` segment (`ConLeche`, `LCNF`, `LeanMLIR`, `LNSym`).
    Returns the banned namespace `Name` when violated. -/
def shadowOriginForbidden? (inv : Inventory) (modName : Name) (n : Name) : Option Name := Id.run do
  let u := userName n
  for (ns, allowedMods) in inv.namespaceOwners do
    if ns.isPrefixOf u && !allowedMods.contains modName then
      return some ns
  if inv.proofPrefixes.any (·.isPrefixOf modName) then
    let parentSegs := nameSegments (nameParent u)
    for ns in inv.bannedShadowNames do
      if hasContiguousSublist (nameSegments ns) parentSegs then
        return some ns
  return none

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
  let cand := ownerDecl env n
  let owner := if (env.getModuleIdxFor? cand).isSome then cand else n
  let file := match env.getModuleIdxFor? owner with
    | some i => s!"lean/{(env.header.moduleNames[i.toNat]!).toString.replace "." "/"}.lean"
    | none => ""
  let _ := leanDir
  let ranges := declRangeExt.find? (level := .server) env owner <|>
    declRangeExt.find? (level := .exported) env owner
  return (file, ranges.map (·.selectionRange.pos.line) |>.getD 0)

/-- Every declaration violating `shadowOriginForbidden?`. Unlike `collectTargets`, this pass also
    inspects `private` and `_`-prefixed declarations so an underscore/private stub cannot evade the
    shadow-namespace ban; it skips `n` only when `n` is a compiler/tactic auxiliary (`isAuxName n`)
    attached to a distinct parent declaration `owner` (`owner != n`) whose own defining module
    satisfies `shadowOriginForbidden?` (e.g. `LeanMLIR.denoteExpr.match_1.splitter` realized lazily
    when a proof splits on grandfathered `LeanMLIR.denoteExpr`). -/
def collectShadowOriginViolations (env : Environment) (leanDir : System.FilePath)
    (inv : Inventory) : IO (Array Violation) := do
  let mut vs := #[]
  for (n, _) in env.constants.toList do
    if isForbidden n then continue
    let some i := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[i.toNat]!
    if isAuxName n &&
       (declRangeExt.find? (level := .server) env n).isNone &&
       (declRangeExt.find? (level := .exported) env n).isNone then
      let owner := ownerDecl env n
      if owner != n then
        if let some oi := env.getModuleIdxFor? owner then
          let ownerMod := env.header.moduleNames[oi.toNat]!
          -- Skip compiler-synthesized auxes: either `owner` is in an allowed grandfather module
          -- (e.g. `LeanMLIR.denoteExpr.match_1.splitter` realized in a proof), or `owner` lives in
          -- the same violating module and will itself be reported.
          if oi == i || (shadowOriginForbidden? inv ownerMod owner).isNone then continue
    let some bannedNs := shadowOriginForbidden? inv modName n | continue
    let (file, line) ← declLoc env leanDir n
    vs := vs.push { target := userName n, forbidden := bannedNs, kind := "shadow-origin",
                    hops := 0, path := [userName n], file, line }
  return vs

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
  let mut vs ← collectShadowOriginViolations env leanDir inv
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
    let witness :=
      if v.kind == "shadow-origin" then "(banned shadow-namespace origin)"
      else " → ".intercalate (v.path.map toString) ++
        (if v.kind == "clone" then " ≅ (canonical body equal)" else "")
    IO.println s!"  {v.kind}\t{v.target}\t→ {v.forbidden}\t{v.file}:{v.line}\t{witness}"

/-! ## Ratchet -/

/-- Allowlist file == violation set (both inclusions). -/
def allowlistEqualsViolations (cur : List AllowEntry) (vs : Array Violation) : Array String := Id.run do
  let mut errs := #[]
  let curKeys : Std.HashSet String := cur.foldl (·.insert ·.key) {}
  for v in vs do
    unless curKeys.contains v.key do
      errs := errs.push s!"violation missing from {allowlistPath}: {v.key} ({v.file}:{v.line})"
  let vKeys : Std.HashSet String := vs.foldl (·.insert ·.key) {}
  for a in cur do
    unless vKeys.contains a.key do
      errs := errs.push s!"stale allowlist entry (violation gone; remove it): {a.key}"
  return errs

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
  -- Working-tree allowlist == current violation set, both inclusions, in EVERY mode. In bootstrap
  -- the base allowlist IS the violation set, so the check above is vacuous there; this one makes
  -- an introducing allowlist that omits an existing violation (e.g. an empty one) fail.
  errs := errs ++ allowlistEqualsViolations cur vs
  -- inventory may not shrink relative to base
  if let some baseInvS ← gitShowAt repo base inventoryPath then
    let bi ← IO.ofExcept (parseInventory baseInvS)
    for m in bi.modules do
      unless inv.modules.contains m do errs := errs.push s!"inventory drops base module {m}"
    for n in bi.namespaces do
      unless inv.namespaces.contains n do errs := errs.push s!"inventory drops base namespace {n}"
    for r in bi.sourceRoots do
      unless inv.sourceRoots.contains r do errs := errs.push s!"inventory drops base source root {r}"
    for p in bi.proofPrefixes do
      unless inv.proofPrefixes.contains p do errs := errs.push s!"inventory drops base proof prefix {p}"
    for (ns, allowedBase) in bi.namespaceOwners do
      match inv.namespaceOwners.find? (·.1 == ns) with
      | none => errs := errs.push s!"inventory drops namespace_owners restriction for {ns}"
      | some (_, allowedCur) =>
        for m in allowedCur do
          unless allowedBase.contains m do
            errs := errs.push s!"inventory widens namespace_owners for {ns} with {m}"
  return errs

/-! ## Self-test -/

def allowJson (vs : List Violation) : String :=
  (Json.mkObj [("schema", (1 : Nat)), ("entries", Json.arr (vs.toArray.map fun v =>
    Json.mkObj [("target", toString v.target), ("forbidden", toString v.forbidden),
                ("kind", v.kind)]))]).pretty ++ "\n"

def invJson (nss : List String) : String :=
  (Json.mkObj [("modules", Json.arr #[]), ("namespaces", Json.arr (nss.toArray.map Json.str)),
               ("source_roots", Json.arr #[])]).pretty ++ "\n"

/-- Fresh git repository whose single commit contains `baseFiles`, with
    `scripts/shadow_allowlist.json` then overwritten in the working tree by `curAllow`.
    Returns the repository and the base commit SHA. -/
def mkRatchetRepo (baseFiles : List (String × String)) (curAllow : String) :
    IO (System.FilePath × String) := do
  let dir ← IO.FS.createTempDir
  let run (args : Array String) : IO String := do
    -- hermetic: ignore global / system / injected (`GIT_CONFIG_COUNT`) config (signing, hooks)
    let env : Array (String × Option String) :=
      #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1"),
        ("GIT_CONFIG_COUNT", some "0")]
    let out ← IO.Process.output { cmd := "git", args := args, cwd := some dir, env := env }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"ratchet test: git {args} failed: {out.stderr}"
    return out.stdout.trimAscii.toString
  discard <| run #["init", "-q"]
  IO.FS.createDirAll (dir / "scripts")
  IO.FS.writeFile (dir / "README") "ratchet fixture\n"
  for (p, c) in baseFiles do IO.FS.writeFile (dir / p) c
  discard <| run #["add", "-A"]
  discard <| run #["-c", "user.name=shadow", "-c", "user.email=shadow@localhost",
    "-c", "commit.gpgsign=false", "commit", "-q", "-m", "base"]
  let sha ← run #["rev-parse", "HEAD"]
  IO.FS.writeFile (dir / allowlistPath) curAllow
  return (dir, sha)

/-- Ratchet fixtures: every case calls the real `checkRatchet` against a real base revision. -/
def ratchetTests (fixtureVs : Array Violation) : IO (Array String) := do
  let pick (t : Name) : List Violation :=
    (fixtureVs.filter (·.target == t)).toList
  let first := pick `ShadowFixtureAllowlisted.first
  let helper := pick `ShadowFixtureAllowlisted.helper
  let second := pick `ShadowFixtureAllowlisted.second
  if first.isEmpty || helper.isEmpty || second.isEmpty then
    return #["ratchet tests: ShadowFixtureAllowlisted fixtures not detected (vacuous)"]
  let inv : Inventory := { modules := [], namespaces := [`ShadowFixtureAllowlisted], sourceRoots := [] }
  let checker := (checkerPath, "-- checker present at base\n")
  let fakeV : Violation := { target := `X.y, forbidden := `LeanNative.Semantics.evalExpr, kind := "call∞" }
  -- (name, base files, working-tree allowlist, violations, inventory, substrings that must ALL
  --  occur in ONE reported error — empty list = must pass with no error)
  let cases : List (String × List (String × String) × String × List Violation × Inventory × List String) := [
    ("clean: allowlist == base == violations → pass",
      [checker, (allowlistPath, allowJson (first ++ helper)), (inventoryPath, invJson ["ShadowFixtureAllowlisted"])],
      allowJson (first ++ helper), first ++ helper, inv, []),
    ("allowlisted-second: new violation in an allowlisted namespace → fail",
      [checker, (allowlistPath, allowJson (first ++ helper))],
      allowJson (first ++ helper), first ++ helper ++ second, inv,
      [s!"NEW violation not in base allowlist: {(second.head!).key}"]),
    ("allowlist addition (even of a real violation) → fail",
      [checker, (allowlistPath, allowJson first)],
      allowJson (first ++ helper), first ++ helper, inv,
      ["allowlist ADDS entry not in base", s!": {(helper.head!).key}"]),
    ("allowlist addition of a fake entry → fail",
      [checker, (allowlistPath, allowJson first)],
      allowJson (first ++ [fakeV]), first, inv,
      ["allowlist ADDS entry not in base", s!": {fakeV.key}"]),
    ("stale entry (violation fixed, entry kept) → fail",
      [checker, (allowlistPath, allowJson (first ++ helper))],
      allowJson (first ++ helper), first, inv,
      [s!"stale allowlist entry (violation gone; remove it): {(helper.head!).key}"]),
    ("entry removed together with its violation → pass",
      [checker, (allowlistPath, allowJson (first ++ helper))],
      allowJson first, first, inv, []),
    ("inventory drops a base namespace → fail",
      [checker, (allowlistPath, allowJson first), (inventoryPath, invJson ["ShadowFixtureAllowlisted", "Dropped"])],
      allowJson first, first, inv, ["inventory drops base namespace Dropped"]),
    ("base has the checker but no allowlist → fail",
      [checker], allowJson first, first, inv, ["has the checker but no"]),
    ("bootstrap: allowlist == violations → pass",
      [], allowJson (first ++ helper), first ++ helper, inv, []),
    ("bootstrap: EMPTY allowlist with existing violations → fail",
      [], allowJson [], first ++ helper, inv,
      ["violation missing from", (first.head!).key]),
    ("bootstrap: allowlist omits one existing violation → fail",
      [], allowJson first, first ++ helper, inv,
      ["violation missing from", (helper.head!).key]),
    ("entry dropped while its violation remains → fail",
      [checker, (allowlistPath, allowJson (first ++ helper))],
      allowJson first, first ++ helper, inv,
      ["violation missing from", (helper.head!).key]),
        ("bootstrap: extra allowlist entry → fail",
          [], allowJson (first ++ [fakeV]), first, inv, ["allowlist ADDS entry not in base", s!": {fakeV.key}"]),
        ("inventory drops proof_module_prefixes entry → fail",
          [checker, (allowlistPath, allowJson first),
           (inventoryPath, (Json.mkObj [("modules", Json.arr #[]), ("namespaces", Json.arr #[Json.str "ShadowFixtureAllowlisted"]),
             ("source_roots", Json.arr #[]), ("proof_module_prefixes", Json.arr #[Json.str "LeanNative.Proofs"])]).pretty ++ "\n")],
          allowJson first, first, { inv with proofPrefixes := [] }, ["inventory drops base proof prefix LeanNative.Proofs"]),
        ("inventory widens namespace_owners → fail",
          [checker, (allowlistPath, allowJson first),
           (inventoryPath, (Json.mkObj [("modules", Json.arr #[]), ("namespaces", Json.arr #[Json.str "ShadowFixtureAllowlisted"]),
             ("source_roots", Json.arr #[]),
             ("namespace_owners", Json.mkObj [("ConLeche", Json.arr #[Json.str "TurboLean.ConLeche"])])]).pretty ++ "\n")],
          allowJson first, first,
          { inv with namespaceOwners := [(`ConLeche, [`TurboLean.ConLeche, `LeanNative.Proofs.Fake])] },
          ["inventory widens namespace_owners for ConLeche with LeanNative.Proofs.Fake"])]
  let mut errs := #[]
  for (label, baseFiles, cur, vs, inv', expected) in cases do
    let (dir, sha) ← mkRatchetRepo baseFiles cur
    let got ← try checkRatchet dir sha inv' vs.toArray
      catch e => pure #[s!"exception: {e}"]
    IO.FS.removeDirAll dir
    let ok := if expected.isEmpty then got.isEmpty
      else got.any fun g => expected.all fun x => (g.splitOn x).length > 1
    IO.println s!"[self-test] ratchet {if ok then "ok  " else "FAIL"} {label}{if got.isEmpty then "" else s!" — {got.toList}"}"
    unless ok do
      errs := errs.push s!"ratchet case `{label}`: expected {if expected.isEmpty then "pass" else s!"{expected}"}, got {got.toList}"
  return errs

/-- The `implemented_by` fixture cannot be a source file (the repository hygiene gate rejects
    the implemented-by attribute everywhere), so it is added to the imported environment here: a real
    kernel-checked definition whose logical body is `unaryLogical`'s (no forbidden constant) and
    whose `implemented_by` attribute names `unaryImpl` (which calls `evalUnaryOp`). -/
def withImplementedByFixture (env : Environment) : IO Environment := do
  let ctx : Core.Context := { fileName := "<shadow-self-test>", fileMap := default,
                              maxHeartbeats := 0, maxRecDepth := 100000 }
  let act : CoreM Environment := do
    let some (.defnInfo v) := (← getEnv).find? `UnrelatedTraversal.unaryLogical
      | throwError "fixture UnrelatedTraversal.unaryLogical missing"
    let n := `ShadowFixtureTraversal.viaImplementedBy
    addDecl (.defnDecl { name := n, levelParams := [], type := v.type, value := v.value,
                         hints := .abbrev, safety := .safe })
    setImplementedBy n `UnrelatedTraversal.unaryImpl
    unless Compiler.getImplementedBy? (← getEnv) n == some `UnrelatedTraversal.unaryImpl do
      throwError "implemented_by not recorded on {n}"
    getEnv
  let (env', _) ← act.toIO ctx { env }
  return env'

def selfTest (env : Environment) (leanDir : System.FilePath) : IO (Array String) := do
  let inv : Inventory := {
    modules := [],
    namespaces := fixtureNamespaces,
    sourceRoots := [],
    namespaceOwners := minNamespaceOwners,
    proofPrefixes := [`ShadowFixtures.ShadowNamespaceStubs],
    bannedShadowNames := minNamespaces
  }
  let env ← withImplementedByFixture env
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
  -- (5) traversal classes: each fixture asserts (target, forbidden evaluator, kind) and, where the
  --     class is isolated, that the witness path goes through the expected intermediate constant.
  let travel : List (Name × Name × String × Option Name × String) := [
    (`ShadowFixtureTraversal.deep, `LeanNative.Semantics.evalBinOp, "call∞",
      some `UnrelatedTraversal.h4, "call∞ through 5 hops"),
    (`ShadowFixtureTraversal.viaInstance, `LeanNative.Semantics.evalBinOp, "call≤3",
      some `UnrelatedTraversal.instDenoteBinOp, "synthesized instance"),
    (`ShadowFixtureTraversal.viaImplementedBy, `LeanNative.Semantics.evalUnaryOp, "call≤3",
      some `UnrelatedTraversal.unaryImpl, "implemented_by (synthesized in env)"),
    (`ShadowFixtureTraversal.viaMacro, `LeanNative.Semantics.evalBinOp, "call≤3",
      none, "macro-expanded call"),
    (`ShadowFixtureTraversal.viaUnsafeRec, `LeanNative.Semantics.evalUnaryOp, "call≤3",
      some `ShadowFixtureTraversal.viaUnsafeRec._unsafe_rec, "_unsafe_rec auxiliary only"),
    (`ShadowFixtureTraversal.viaProofAux, `LeanNative.Semantics.evalBinOp, "call≤3",
      none, "proof auxiliary only (_proof_n)"),
    (`ShadowFixtureTraversal.viaMatcher, `LeanNative.Semantics.evalBinOp, "call≤3",
      none, "matcher auxiliary"),
    (`ShadowFixtureTraversal.viaInductive, `LeanNative.Semantics.evalBinOp, "call≤3",
      some `UnrelatedTraversal.AddsTo, "inductive → ctor/recursor types")]
  for (t, f, k, via?, label) in travel do
    match r.violations.find? fun v => v.target == t && v.forbidden == f && v.kind == k with
    | none => errs := errs.push s!"fixture traversal [{label}]: expected {t} → {f} ({k})"
    | some v =>
      if let some via := via? then
        unless v.path.contains via do
          errs := errs.push s!"fixture traversal [{label}]: witness {v.path} does not pass through {via}"
  -- `viaProofAux`'s only forbidden mention lives in an abstracted `_proof_n` auxiliary
  if let some v := r.violations.find? (·.target == `ShadowFixtureTraversal.viaProofAux) then
    unless v.path.any (fun n => match n with | .str _ s => s.startsWith "_proof_" | _ => false) do
      errs := errs.push s!"fixture traversal [proof aux]: witness {v.path} skips the `_proof_n` auxiliary"
  -- untargeted helpers in `UnrelatedTraversal` must not be reported themselves
  if r.violations.any (fun v => (`UnrelatedTraversal).isPrefixOf v.target) then
    errs := errs.push "fixture traversal: un-inventoried helper namespace reported as a target"
  -- (6) shadow-origin negative fixtures (local `ConLeche`/`LCNF`/`LeanMLIR`/`LNSym` stubs in proofs,
  --     including toy equality `CICValid` and empty-list `parseOleanShard`, referencing zero `eval*`)
  let originExpected : List (Name × Name × String) := [
    (`ShadowFixtureOrigin.ConLeche.CICValid, `ConLeche, "toy equality CICValid stub"),
    (`ShadowFixtureOrigin.ConLeche.parseOleanShard, `ConLeche, "size-only empty-decls parseOleanShard stub"),
    (`ShadowFixtureOrigin.ConLeche.verify_toy_sound, `ConLeche, "theorem inside local ConLeche proof stub"),
    (`ShadowFixtureOrigin.ConLeche.olean_toy_sound, `ConLeche, "theorem over fake parseOleanShard stub"),
    (`ShadowFixtureOrigin.ConLeche._privateToyStub, `ConLeche, "private underscore stub in ConLeche"),
    (`ShadowFixtureOrigin.LCNF.evalToy, `LCNF, "local LCNF shadow namespace in proofs"),
    (`ShadowFixtureOrigin.LeanMLIR.denoteToy, `LeanMLIR, "local LeanMLIR shadow namespace in proofs"),
    (`ShadowFixtureOrigin.LNSym.stepToy, `LNSym, "local LNSym shadow namespace in proofs")]
  for (t, ns, label) in originExpected do
    unless find t ns "shadow-origin" do
      errs := errs.push s!"fixture shadow-origin [{label}]: expected {t} → {ns} (shadow-origin)"
  -- also verify top-level namespace owner check directly on synthetic module names
  unless shadowOriginForbidden? inv `LeanNative.Proofs.Fake `ConLeche.CICValid == some `ConLeche do
    errs := errs.push "shadowOriginForbidden? failed to flag top-level ConLeche outside TurboLean.ConLeche"
  unless shadowOriginForbidden? inv `TurboLean.ConLeche `ConLeche.CICValid == none do
    errs := errs.push "shadowOriginForbidden? falsely flagged grandfathered TurboLean.ConLeche"
  unless shadowOriginForbidden? inv `LeanNative.Proofs.LCNFBridgeProofs `LeanNative.Proofs.evalLCNF == none do
    errs := errs.push "shadowOriginForbidden? falsely flagged non-shadow Proof declaration"
  -- (4) + ratchet: the REAL `checkRatchet` against a temporary git repository
  errs := errs ++ (← ratchetTests r.violations)
  -- forbidden set sanity: auxiliaries are forbidden
  unless isForbidden `LeanNative.Semantics.evalBinOp.match_1 && !isForbidden `LeanNative.Semantics.Val.toU256? do
    errs := errs.push "forbidden-set predicate wrong"
  IO.println s!"[self-test] {if errs.isEmpty then "PASS" else "FAIL"}: direct-call, verbatim-clone, helper-clone, bitvec-only, {travel.length} traversal classes, {originExpected.length} shadow-origin stubs, ratchet cases"
  (← IO.getStdout).flush
  return errs

/-- Output emitted by a single `--worker-batch` subprocess. -/
structure WorkerPayload where
  report : Report
  seenMods : Array Name
  seenNs : Array Name
  seenForbidden : Array Name
  selfTestErrs : Array String
  deriving Inhabited

def Violation.fromJson (j : Json) : Except String Violation := do
  return {
    target := strName (← (j.getObjValD "target").getStr?),
    forbidden := strName (← (j.getObjValD "forbidden").getStr?),
    kind := ← (j.getObjValD "kind").getStr?,
    hops := ← (j.getObjValD "hops").getNat?,
    file := ← (j.getObjValD "file").getStr?,
    line := ← (j.getObjValD "line").getNat?,
    path := (← (j.getObjValD "path").getArr?).toList.filterMap fun x =>
      match x.getStr? with | .ok s => some (strName s) | .error _ => none
  }

def WorkerPayload.toJson (w : WorkerPayload) : Json :=
  Json.mkObj [
    ("targetLocs", Json.arr (w.report.targetLocs.map fun (n, f, l) =>
      Json.mkObj [("name", toString n), ("file", f), ("line", l)])),
    ("violations", Json.arr (w.report.violations.map Violation.toJson)),
    ("forbidden", Json.arr (w.report.forbidden.map (Json.str ∘ toString))),
    ("seenMods", Json.arr (w.seenMods.map (Json.str ∘ toString))),
    ("seenNs", Json.arr (w.seenNs.map (Json.str ∘ toString))),
    ("seenForbidden", Json.arr (w.seenForbidden.map (Json.str ∘ toString))),
    ("selfTestErrs", Json.arr (w.selfTestErrs.map Json.str))
  ]

def WorkerPayload.fromJson (s : String) : Except String WorkerPayload := do
  let j ← Json.parse s
  let locs ← (← (j.getObjValD "targetLocs").getArr?).mapM fun x => do
    return (strName (← (x.getObjValD "name").getStr?),
            ← (x.getObjValD "file").getStr?,
            ← (x.getObjValD "line").getNat?)
  let vs ← (← (j.getObjValD "violations").getArr?).mapM Violation.fromJson
  let fs ← (jsonStrList j "forbidden")
  let sm ← (jsonStrList j "seenMods")
  let sn ← (jsonStrList j "seenNs")
  let sf ← (jsonStrList j "seenForbidden")
  let se ← (jsonStrList j "selfTestErrs")
  return {
    report := { targets := locs.map (·.1), targetLocs := locs, violations := vs,
                forbidden := (fs.map strName).toArray },
    seenMods := (sm.map strName).toArray,
    seenNs := (sn.map strName).toArray,
    seenForbidden := (sf.map strName).toArray,
    selfTestErrs := se.toArray
  }

/-- Parse direct imports of a `.lean` source file using Lean's own header parser. -/
def parseSourceImports (src : System.FilePath) : IO (Array Name) := do
  let txt ← IO.FS.readFile src
  let ictx := Parser.mkInputContext txt src.toString
  let (hdr, _, msgs) ← Parser.parseHeader ictx
  if msgs.hasErrors then
    let mut es := #[]
    for m in msgs.toList do es := es.push (← m.toString)
    throw <| IO.userError s!"header parse errors in {src}: {"; ".intercalate es.toList}"
  return (Elab.headerToImports hdr (includeInit := false)).map (·.module)

/-- Locate an actually-existing `.olean` on `sp` (unlike `SearchPath.findWithExt`, which matches
    by first package component even when the target `.olean` file itself is absent). -/
def findExistingOLean? (sp : SearchPath) (m : Name) : IO (Option System.FilePath) := do
  if let some p ← SearchPath.findWithExt sp "olean" m then
    if ← p.pathExists then return some p
  let rel := (m.toString.replace "." "/") ++ ".olean"
  for d in sp do
    let p := d / rel
    if ← p.pathExists then return some p
  return none

partial def symlinkTree (src dst : System.FilePath) : IO Unit := do
  if ← src.isDir then
    IO.FS.createDirAll dst
    for entry in ← src.readDir do
      symlinkTree entry.path (dst / entry.fileName)
  else if !(← dst.pathExists) then
    let out ← IO.Process.output { cmd := "ln", args := #["-s", src.toString, dst.toString] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"ln -s {src} {dst} failed: {out.stderr}"

/-- Because Lean's `SearchPath.findWithExt` resolves a root package prefix (`TurboLean`) to the
    FIRST search-path directory containing either `TurboLean.olean` or `TurboLean/`, placing a
    newly-compiled standalone `TurboLean.olean` in `scratchDir` would hide `TurboLean/*.olean` in
    `.lake/build/lib/lean` unless `scratchDir` mirrors existing artifacts under that root prefix. -/
def mirrorRootPackage (curSp : SearchPath) (scratchDir : System.FilePath) (pkg : String) :
    IO Unit := do
  for d in curSp do
    if ← d.isDir then
      let realD ← IO.FS.realPath d
      let rootOlean := realD / s!"{pkg}.olean"
      let dstOlean := scratchDir / s!"{pkg}.olean"
      if (← rootOlean.pathExists) && !(← dstOlean.pathExists) then
        let out ← IO.Process.output { cmd := "ln", args := #["-s", rootOlean.toString, dstOlean.toString] }
        unless out.exitCode == 0 do
          throw <| IO.userError s!"ln -s {rootOlean} {dstOlean} failed: {out.stderr}"
      let subDir := realD / pkg
      if ← subDir.isDir then
        symlinkTree subDir (scratchDir / pkg)

/-- Compile any discovered source module lacking a Lake `.olean` (such as a standalone
    `<root>.lean` excluded by `.submodules` globs) into `scratchDir` in topological import order,
    prepending `scratchDir` to `searchPathRef` and returning the updated `LEAN_PATH`. Fails closed
    on missing sources, cyclic standalone imports, or compiler failure. -/
def compileMissingModules (leanDir scratchDir : System.FilePath) (mods : Array Name) :
    IO String := do
  let leanBin ← IO.appPath
  let baseLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let sep := System.SearchPath.separator.toString
  let curSp ← searchPathRef.get
  let mut pending : Array (Name × System.FilePath × Array Name) := #[]
  for m in mods do
    if (← findExistingOLean? curSp m).isNone then
      let src := leanDir / s!"{m.toString.replace "." "/"}.lean"
      unless ← src.pathExists do
        throw <| IO.userError s!"discovered module {m} has neither .olean nor source at {src}"
      let deps ← parseSourceImports src
      pending := pending.push (m, src, deps)
  if pending.isEmpty then
    let spStrs := curSp.map (·.toString)
    return sep.intercalate (if baseLeanPath.isEmpty then spStrs else spStrs ++ [baseLeanPath])
  let mut mirrored : Std.HashSet String := {}
  for (m, _, _) in pending do
    let pkg := m.getRoot.toString
    unless mirrored.contains pkg do
      mirrored := mirrored.insert pkg
      mirrorRootPackage curSp scratchDir pkg
  let fullSp := scratchDir :: curSp
  searchPathRef.set fullSp
  let spStrs := fullSp.map (·.toString)
  let newLeanPath := sep.intercalate (if baseLeanPath.isEmpty then spStrs else spStrs ++ [baseLeanPath])
  while !pending.isEmpty do
    let pendNames : Std.HashSet Name := pending.foldl (fun s (m, _, _) => s.insert m) {}
    let (ready, rest) := pending.partition fun (_, _, deps) => !deps.any pendNames.contains
    if ready.isEmpty then
      throw <| IO.userError s!"import cycle among unbuilt standalone modules: {pending.map (·.1)}"
    for (m, src, _) in ready do
      let outOlean := scratchDir / s!"{m.toString.replace "." "/"}.olean"
      if let some parent := outOlean.parent then IO.FS.createDirAll parent
      stage s!"compiling standalone module {m} → {outOlean}"
      let res ← IO.Process.output {
        cmd := leanBin.toString,
        args := #["-DautoImplicit=false", src.toString, "-R", leanDir.toString, "-o", outOlean.toString],
        cwd := some leanDir,
        env := #[("LEAN_PATH", some newLeanPath)]
      }
      unless res.exitCode == 0 do
        throw <| IO.userError s!"compiling standalone module {m} failed:\n{res.stdout}\n{res.stderr}"
    pending := rest
  return newLeanPath

/-- Partition `mods` into importable environments by inspecting `.olean` headers (`readModuleData`):
    any module that defines `main` (or transitively imports one that defines `main`) is grouped by
    the set of `main`-defining modules in its transitive closure. A pure library base (0 `main`s)
    plus `k` distinct single-owner `main` cones yields `k` batches when `k ≥ 1` (each cone imports
    the entire library base alongside its compatible `main`-cone modules), or 1 batch when `k = 0`.
    Modules that transitively pull ≥ 2 distinct `main` owners cannot be imported by Lean at all and
    fail closed immediately. -/
partial def mainConeOwnersOf (sp : SearchPath)
    (cache : IO.Ref (Std.HashMap Name (Std.HashSet Name))) (m : Name) :
    IO (Std.HashSet Name) := do
  if let some res := (← cache.get)[m]? then return res
  let fm := freshName m
  cache.modify (·.insert fm {})
  let some olean ← findExistingOLean? sp fm
    | return {}  -- core / external module outside local search path or Init
  let (md, _reg) ← readModuleData olean
  let hasMain := md.constNames.contains `main
  let deps := md.imports.map fun imp => freshName imp.module
  let mut s : Std.HashSet Name :=
    if hasMain then ({} : Std.HashSet Name).insert fm else {}
  for d in deps do
    for o in (← mainConeOwnersOf sp cache d) do s := s.insert o
  cache.modify (·.insert fm s)
  return s

def partitionByMainCones (mods : Array Name) : IO (Array (Array Name)) := do
  let sp ← searchPathRef.get
  let cache ← IO.mkRef ({} : Std.HashMap Name (Std.HashSet Name))
  let mut pureLibs : Array Name := #[]
  let mut byOwner : Std.HashMap Name (Array Name) := {}
  let mut ownerOrder : Array Name := #[]
  for m in mods do
    let os := (← mainConeOwnersOf sp cache m).toArray
    if os.isEmpty then
      pureLibs := pureLibs.push m
    else if os.size == 1 then
      let o := os[0]!
      unless byOwner.contains o do ownerOrder := ownerOrder.push o
      byOwner := byOwner.insert o ((byOwner[o]?.getD #[]).push m)
    else
      throw <| IO.userError s!"module {m} transitively imports conflicting `main` definitions: {os}"
  let sortedOwners := ownerOrder.qsort (·.toString < ·.toString)
  if sortedOwners.isEmpty then
    return #[pureLibs]
  else
    return sortedOwners.map fun o => pureLibs ++ (byOwner[o]?.getD #[])

/-- Self-test for `compileMissingModules` + `partitionByMainCones`: builds an isolated directory
    of synthetic `.lean` modules with two conflicting `def main` owners (`FakePkg.Sub`, `FakeExeB`),
    an unbuilt standalone `<root>.lean` module `FakePkg` importing `FakePkg.Sub` while
    `FakePkg/Sub.olean` already lives in a separate `built` search-path directory (exact replica of
    `TurboLean.lean` + `.lake/build/lib/lean/TurboLean/ZygoteWorker.olean`), and a shared library
    `FakeLib`, then verifies scratch compilation, symlink mirroring, and `main`-cone partitioning. -/
def partitionAndStandaloneTests (leanDir : System.FilePath) : IO (Array String) := do
  let tmp ← IO.FS.createTempDir
  let mut errs := #[]
  try
    let srcDir := tmp / "src"
    let builtDir := tmp / "built"
    let scratch := tmp / "olean"
    IO.FS.createDirAll (srcDir / "FakePkg")
    IO.FS.createDirAll builtDir
    IO.FS.createDirAll scratch
    IO.FS.writeFile (srcDir / "FakeLib.lean") "namespace FakeLib\ndef x : Nat := 1\nend FakeLib\n"
    IO.FS.writeFile (srcDir / "FakePkg" / "Sub.lean") "import FakeLib\ndef main : IO Unit := pure ()\n"
    IO.FS.writeFile (srcDir / "FakeExeB.lean") "import FakeLib\ndef main : IO Unit := pure ()\n"
    IO.FS.writeFile (srcDir / "FakePkg.lean") "import FakePkg.Sub\nnamespace FakePkg\ndef y : Nat := FakeLib.x\nend FakePkg\n"
    IO.FS.writeFile (srcDir / "FakeDual.lean") "import FakePkg.Sub\nimport FakeExeB\ndef z : Nat := 0\n"
    let savedSp ← searchPathRef.get
    try
      -- Pre-compile FakeLib, FakePkg.Sub, FakeExeB into `builtDir`, leaving standalone `FakePkg.lean` unbuilt
      discard <| compileMissingModules srcDir builtDir #[`FakeLib, `FakePkg.Sub, `FakeExeB]
      searchPathRef.set (builtDir :: savedSp)
      discard <| compileMissingModules srcDir scratch #[`FakeLib, `FakePkg.Sub, `FakeExeB, `FakePkg]
      unless ← (scratch / "FakePkg.olean").pathExists do
        errs := errs.push "standalone-compile test: FakePkg.olean was not produced"
      unless ← (scratch / "FakePkg" / "Sub.olean").pathExists do
        errs := errs.push "standalone-compile test: FakePkg/Sub.olean was not mirrored into scratch"
      let batches ← partitionByMainCones #[`FakeLib, `FakePkg.Sub, `FakeExeB, `FakePkg]
      if batches.size != 2 then
        errs := errs.push s!"partition test: expected 2 main-cone batches, got {batches.size}: {batches}"
      else
        let bA := batches.find? (·.contains `FakePkg.Sub) |>.getD #[]
        let bB := batches.find? (·.contains `FakeExeB) |>.getD #[]
        unless bA.contains `FakeLib && bA.contains `FakePkg && !bA.contains `FakeExeB do
          errs := errs.push s!"partition test: FakePkg.Sub batch malformed: {bA}"
        unless bB.contains `FakeLib && !bB.contains `FakePkg.Sub && !bB.contains `FakePkg do
          errs := errs.push s!"partition test: FakeExeB batch malformed: {bB}"
      -- Verify that a module importing two conflicting `main`s fails closed
      let dualFailed ← try
        discard <| compileMissingModules srcDir scratch #[`FakeDual]
        pure false
      catch _ => pure true
      unless dualFailed do
        errs := errs.push "partition test: FakeDual importing two `main`s should fail compilation"
    finally
      searchPathRef.set savedSp
    let _ := leanDir
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()
  IO.println s!"[self-test] {if errs.isEmpty then "ok  " else "FAIL"} standalone compile + main-cone partitioning"
  return errs

/-! ## Driver -/

structure Args where
  base : Option String := none
  jsonOut : Option String := none
  coverageOut : Option String := none
  selfTest : Bool := false
  bootstrap : Bool := false
  workerBatch : Option String := none
  workerOut : Option String := none

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--base" :: r :: rest, a => parseArgs rest { a with base := some r }
  | "--json-out" :: p :: rest, a => parseArgs rest { a with jsonOut := some p }
  | "--coverage-out" :: p :: rest, a => parseArgs rest { a with coverageOut := some p }
  | "--self-test" :: rest, a => parseArgs rest { a with selfTest := true }
  | "--bootstrap" :: rest, a => parseArgs rest { a with bootstrap := true }
  | "--worker-batch" :: m :: rest, a => parseArgs rest { a with workerBatch := some m }
  | "--worker-out" :: o :: rest, a => parseArgs rest { a with workerOut := some o }
  | x :: _, _ => .error s!"unknown argument {x}"

/-- Execute one isolated environment import + analysis in a fresh OS process so `.olean`
    compacted regions are never re-mapped across environments. -/
unsafe def runWorkerBatch (args : Args) (modsFile outFile : String) : IO UInt32 := do
  let leanDir ← IO.currentDir
  let repo := leanDir / ".."
  let inv ← IO.ofExcept (parseInventory (← IO.FS.readFile (repo / inventoryPath)))
  let modLines := (← IO.FS.readFile modsFile).splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  let mods := (modLines.map fun l => strName l.trimAscii.toString).toArray
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := mods.map fun m => ({ module := m } : Import)
  stage s!"worker import #{mods.size} (last: {mods.back?})"
  let env ← importModules imports {} (loadExts := false)
  let mut seenMods := #[]
  for m in inv.modules do
    if (env.getModuleIdx? m).isSome then seenMods := seenMods.push m
  let mut seenNs := #[]
  for n in inv.namespaces do
    if env.constants.toList.any (fun (c, _) => n.isPrefixOf (userName c)) then seenNs := seenNs.push n
  let mut seenForbidden := #[]
  for f in requiredForbidden do
    if env.contains f then seenForbidden := seenForbidden.push f
  let selfTestErrs ← if args.selfTest then selfTest env leanDir else pure #[]
  let r ← analyze env leanDir inv
  let payload : WorkerPayload := { report := r, seenMods, seenNs, seenForbidden, selfTestErrs }
  IO.FS.writeFile outFile (payload.toJson.compress ++ "\n")
  return 0

unsafe def run (args : Args) : IO UInt32 := do
  if let some modsFile := args.workerBatch then
    let some outFile := args.workerOut
      | throw <| IO.userError "--worker-batch requires --worker-out"
    return ← runWorkerBatch args modsFile outFile
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
  for p in minProofPrefixes do
    unless inv.proofPrefixes.contains p do errs := errs.push s!"inventory missing pinned proof prefix {p}"
  for (ns, reqMods) in minNamespaceOwners do
    match inv.namespaceOwners.find? (·.1 == ns) with
    | none => errs := errs.push s!"inventory missing namespace_owners entry for {ns}"
    | some (_, curMods) =>
      for m in curMods do
        unless reqMods.contains m do
          errs := errs.push s!"inventory namespace_owners widens {ns} beyond pinned {reqMods} with {m}"
  let mut modsArr ← discoverModules leanDir inv.sourceRoots
  for m in inv.modules do
    unless modsArr.contains m do errs := errs.push s!"pinned module {m} has no source file"
  if args.selfTest then modsArr := modsArr.push `ShadowFixtures
  initSearchPath (← findSysroot)
  if args.selfTest then
    errs := errs ++ (← partitionAndStandaloneTests leanDir)
  let scratchDir ← IO.FS.createTempDir
  try
    let workerLeanPath ← compileMissingModules leanDir scratchDir modsArr
    let sp ← searchPathRef.get
    for m in modsArr do
      if (← findExistingOLean? sp m).isNone then
        errs := errs.push s!"module {m} has no .olean after standalone compilation"
    let envSets ← partitionByMainCones modsArr
    let leanBin ← IO.appPath
    let scriptPath := repo / checkerPath
    let mut report? : Option Report := none
    let mut seenMods : Std.HashSet Name := {}
    let mut seenNs : Std.HashSet Name := {}
    let mut seenForbidden : Std.HashSet Name := {}
    for idx in [0:envSets.size] do
      let mods := envSets[idx]!
      let modsFile := scratchDir / s!"batch_{idx}.mods"
      let outFile := scratchDir / s!"batch_{idx}.json"
      IO.FS.writeFile modsFile ("\n".intercalate (mods.toList.map toString) ++ "\n")
      let mut wArgs := #["--run", scriptPath.toString,
                         "--worker-batch", modsFile.toString,
                         "--worker-out", outFile.toString]
      if idx == 0 && args.selfTest then wArgs := wArgs.push "--self-test"
      stage s!"spawn worker #{idx + 1}/{envSets.size} ({mods.size} modules, last: {mods.back?})"
      let child ← IO.Process.spawn {
        cmd := leanBin.toString,
        args := wArgs,
        cwd := some leanDir,
        env := #[("LEAN_PATH", some workerLeanPath)],
        stdout := .inherit,
        stderr := .inherit
      }
      let code ← child.wait
      unless code == 0 do
        throw <| IO.userError s!"worker batch #{idx + 1} failed with exit code {code}"
      let payload ← IO.ofExcept (WorkerPayload.fromJson (← IO.FS.readFile outFile))
      for m in payload.seenMods do seenMods := seenMods.insert m
      for n in payload.seenNs do seenNs := seenNs.insert n
      for f in payload.seenForbidden do seenForbidden := seenForbidden.insert f
      errs := errs ++ payload.selfTestErrs
      report? := some (match report? with | some a => a.merge payload.report | none => payload.report)
    for m in inv.modules do
      unless seenMods.contains m do errs := errs.push s!"pinned module {m} not imported"
    for n in inv.namespaces do
      unless seenNs.contains n do errs := errs.push s!"pinned namespace {n} has no declarations (missing/unimported)"
    for f in requiredForbidden do
      unless seenForbidden.contains f do errs := errs.push s!"forbidden evaluator {f} missing from environment"
    stage "all environments analyzed"
    let r := report?.get!
    IO.println s!"[shadow-semantics] {modsArr.size} modules imported ({envSets.size} isolated worker environments), {r.targets.size} target declarations, {r.forbidden.size} forbidden evaluators"
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
        errs := errs ++ allowlistEqualsViolations cur r.violations
    IO.FS.removeDirAll scratchDir
  catch e =>
    try IO.FS.removeDirAll scratchDir catch _ => pure ()
    throw e
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
