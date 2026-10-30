import Lean
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
deriving instance BEq for Lean.InductiveVal, Lean.QuotKind, Lean.QuotVal, Lean.ConstantInfo
namespace B2c
@[extern "b2c_cpu_ns"] opaque cpuNS : IO Nat
structure RS where
  env : Kernel.Environment
  todo : NameSet := {}
  pending : NameSet := {}
  summedNS : Nat := 0
  calls : Nat := 0
structure RC where
  infos : NameMap ConstantInfo
  mod : String
  out : IO.FS.Stream
abbrev R := ReaderT RC (StateRefT RS IO)
def emit (j : Json) : R Unit := do (← read).out.putStrLn j.compress
def fail (s : String) : R Unit := throw <| IO.userError s

def checked (decl : Declaration) (names : List Name) (kind : String) (duplicate := false) : R Unit := do
  let opts := ({} : Options).set `maxRecDepth (100000 : Nat) |>.set `maxHeartbeats (0 : Nat)
  let env := (← get).env
  let a ← cpuNS
  let result := env.addDecl opts decl
  let env' ← match result with
    | .ok e => pure e
    | .error e => throw <| IO.userError (← e.toMessageData {} |>.toString)
  let z ← cpuNS
  let dt := z-a
  modify fun st => { st with env := if duplicate then env else env', summedNS := st.summedNS+dt, calls := st.calls+1 }
  emit <| Json.mkObj [("event", .str "kernel"), ("module", .str (← read).mod),
    ("names", toJson (names.map Name.toString)), ("kind", .str kind),
    ("cpu_ns", toJson dt), ("duplicate_rechecked", toJson duplicate)]

mutual
partial def visit (name : Name) : R Unit := do
  unless (← get).todo.contains name do return
  if (← get).pending.contains name then return
  let some ci := (← read).infos.find? name | return
  modify fun st => {st with pending := st.pending.insert name}
  let infos := (← read).infos
  match ci with
  | .ctorInfo v => visit v.induct
  | .recInfo v => for a in v.all do visit a
  | .inductInfo v =>
    if let some existing := (← get).env.find? name then
      if existing != ci then fail s!"generated inductive differs: {name}"
    else
      let all := v.all.map fun n => (infos.find? n).get!
      for a in v.all do modify fun st => {st with pending := st.pending.insert a}
      let types := all.map fun c => ({name := c.name, type := c.type, ctors := c.inductiveVal!.ctors.map fun cn =>
          {name := cn, type := (infos.find? cn).get!.type}} : InductiveType)
      for ty in types do
        visitDeps ty.type
        for ctor in ty.ctors do visitDeps ctor.type
      checked (.inductDecl v.levelParams v.numParams types v.isUnsafe) v.all "inductive"
      for a in v.all do modify fun st => {st with todo := st.todo.erase a, pending := st.pending.erase a}
  | .quotInfo _ =>
    unless (← get).env.quotInit do
      visit `Eq
      checked .quotDecl [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] "quotient"
  | .defnInfo v =>
    if v.safety != .safe then
      let vals := v.all.map fun n => (match (infos.find? n).get! with | .defnInfo val => val | _ => panic! "expected definition")
      for a in v.all do modify fun st => {st with pending := st.pending.insert a}
      for val in vals do visitDeps val.type; visitDeps val.value
      checked (.mutualDefnDecl vals) v.all "definition"
      for a in v.all do modify fun st => {st with todo := st.todo.erase a, pending := st.pending.erase a}
    else
      visitDeps v.type; visitDeps v.value
      checked (.defnDecl v) [name] "definition"
  | .thmInfo v =>
    visitDeps v.type; visitDeps v.value
    if ((← get).env.find? name).isSome then
      let fresh := Name.str name s!"b2c_duplicate_{(← get).calls}"
      checked (.thmDecl {v with name := fresh}) [name] "theorem" true
    else checked (.thmDecl v) [name] "theorem"
  | .opaqueInfo v =>
    visitDeps v.type; visitDeps v.value
    checked (.opaqueDecl v) [name] "opaque"
  | .axiomInfo v =>
    visitDeps v.type
    checked (.axiomDecl v) [name] "axiom"
  modify fun st => {st with todo := st.todo.erase name, pending := st.pending.erase name}
partial def visitDeps (e : Expr) : R Unit := do
  for a in e.foldConsts ({} : NameSet) (fun n st => st.insert n) do visit a
end

def replay (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let out ← IO.getStdout
  let start ← cpuNS
  let wallStart ← IO.monoNanosNow
  let source ← importModules (args.toArray.map fun m => {module := m.toName}) {} (loadExts := false)
  let importEnd ← cpuNS
  let empty ← mkEmptyEnvironment
  let mut state : RS := { env := empty.toKernelEnv }
  for i in [:source.header.moduleData.size] do
    let md := source.header.moduleData[i]!
    let mod := source.header.modules[i]!.module.toString
    let mut infos : NameMap ConstantInfo := {}
    let mut todo : NameSet := {}
    for ci in md.constants do
      if (infos.find? ci.name).isSome then throw <| IO.userError s!"duplicate stored name within {mod}: {ci.name}"
      infos := infos.insert ci.name ci
      todo := todo.insert ci.name
    state := {state with todo, pending := {}}
    let a ← cpuNS
    let (_, st) ← ((do
      for ci in md.constants do visit ci.name
      -- All generated constructors/recursors must match the imported ConstantInfo.
      for ci in md.constants do
        if ci matches .ctorInfo _ | .recInfo _ then
          if (← get).env.find? ci.name != some ci then fail s!"generated declaration differs: {ci.name}"
      unless (← get).todo.isEmpty do fail s!"unvisited declarations in {mod}"
      : R Unit).run {infos, mod, out}).run state
    let z ← cpuNS
    out.putStrLn <| (Json.mkObj [("event", .str "module_replay"), ("module", .str mod),
      ("constants", toJson md.constants.size), ("cpu_ns", toJson (z-a)),
      ("kernel_cpu_ns", toJson (st.summedNS-state.summedNS)),
      ("calls", toJson (st.calls-state.calls))]).compress
    state := st
  let stop ← cpuNS
  let wallStop ← IO.monoNanosNow
  if state.summedNS > stop-start then throw <| IO.userError "summed kernel CPU exceeds replay CPU"
  out.putStrLn <| (Json.mkObj [("event", .str "total"), ("cpu_clock", .str "CLOCK_PROCESS_CPUTIME_ID"), ("cpu_ns", toJson (stop-start)),
    ("wall_ns", toJson (wallStop-wallStart)), ("import_cpu_ns", toJson (importEnd-start)),
    ("kernel_cpu_ns", toJson state.summedNS), ("overhead_cpu_ns", toJson (stop-start-state.summedNS)),
    ("calls", toJson state.calls), ("sum_le_total_cpu", toJson (decide (state.summedNS ≤ stop-start)))]).compress
end B2c

def main (args : List String) : IO Unit := B2c.replay args
