import Lean

open Lean Elab Command in
/-- Independent oracle: persisted, user-facing theorem constants of the current module.
Private names are demangled. Projections, internal proof/equation lemmas, and
`where` auxiliaries owned by a parent theorem are not separate user-facing targets.
Examples are not persisted, and structure instances are definitions, not theorem constants. -/
elab "#dump_corpus_theorems" : command => do
  let env ← getEnv
  let mut names : Array String := #[]
  for (name, info) in env.constants.toList do
    let userName := privateToUserName name
    if info matches .thmInfo _ then
      let rec hasTheoremParent : Name → Bool
        | .anonymous => false
        | .str p s => (env.find? (.str p s)).any (fun ci => ci matches .thmInfo _) || hasTheoremParent p
        | .num p i => (env.find? (.num p i)).any (fun ci => ci matches .thmInfo _) || hasTheoremParent p
      if (env.getModuleIdxFor? name).isNone && !userName.isInternal &&
          !(env.isProjectionFn name) && !hasTheoremParent name.getPrefix then
        names := names.push userName.toString
  for name in names.qsort (· < ·) do
    logInfo m!"CORPUS_THEOREM {name}"
