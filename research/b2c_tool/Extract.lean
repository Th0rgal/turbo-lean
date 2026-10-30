import Lean
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
deriving instance Repr for Lean.ReducibilityHints
namespace B2c
abbrev J := Json
def arr (xs : List J) : J := .arr xs.toArray
def s (v : String) : J := .str v
def n (v : Nat) : J := toJson v
def b (v : Bool) : J := toJson v
def nm : Name → J
  | .anonymous => arr [s "anon"]
  | .str p v => arr [s "str", nm p, s v]
  | .num p v => arr [s "num", nm p, n v]
def ns (xs : List Name) : J := arr (xs.map nm)
def lv : Level → J
  | .zero => arr [s "zero"]
  | .succ a => arr [s "succ", lv a]
  | .max a c => arr [s "max", lv a, lv c]
  | .imax a c => arr [s "imax", lv a, lv c]
  | .param a => arr [s "param", nm a]
  | .mvar a => arr [s "mvar", nm a.name]
structure ES where
  memo : ExprMap Nat := {}
  nodes : Array J := #[]
abbrev E := StateM ES
partial def ex (e : Expr) : E J := do
  if let some i := (← get).memo[e]? then return n i
  let node ← match e with
    | .bvar i => pure <| arr [s "bvar", n i]
    | .fvar i => pure <| arr [s "fvar", nm i.name]
    | .mvar i => pure <| arr [s "mvar", nm i.name]
    | .sort l => pure <| arr [s "sort", lv l]
    | .const a ls => pure <| arr [s "const", nm a, arr (ls.map lv)]
    | .app f a => pure <| arr [s "app", ← ex f, ← ex a]
    | .lam a t v bi => pure <| arr [s "lam", nm a, s (reprStr bi), ← ex t, ← ex v]
    | .forallE a t v bi => pure <| arr [s "forall", nm a, s (reprStr bi), ← ex t, ← ex v]
    | .letE a t v body nondep => pure <| arr [s "let", nm a, b nondep, ← ex t, ← ex v, ← ex body]
    | .lit (.natVal v) => pure <| arr [s "nat", n v]
    | .lit (.strVal v) => pure <| arr [s "string", s v]
    | .mdata md e => pure <| arr [s "mdata", s (reprStr md), ← ex e]
    | .proj a i e => pure <| arr [s "proj", nm a, n i, ← ex e]
  let i := (← get).nodes.size
  modify fun st => { memo := st.memo.insert e i, nodes := st.nodes.push node }
  return n i
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
def payload (ci : ConstantInfo) (iface : Bool) : E J := do
  let base := [s (kind ci), nm ci.name, ns ci.levelParams, ← ex ci.type]
  let more : List J ← match ci with
    | .axiomInfo v => pure [b v.isUnsafe]
    | .defnInfo v => pure [← ex v.value, s (reprStr v.hints), s (reprStr v.safety), ns v.all]
    | .thmInfo v => do
      if iface then pure [] else pure [← ex v.value, ns v.all]
    | .opaqueInfo v => pure [← ex v.value, b v.isUnsafe, ns v.all]
    | .inductInfo v => pure [n v.numParams, n v.numIndices, ns v.all, ns v.ctors,
        n v.numNested, b v.isRec, b v.isUnsafe, b v.isReflexive]
    | .ctorInfo v => pure [nm v.induct, n v.cidx, n v.numParams, n v.numFields, b v.isUnsafe]
    | .recInfo v => do
      let rs ← v.rules.mapM fun r => return arr [nm r.ctor, n r.nfields, ← ex r.rhs]
      pure [ns v.all, n v.numParams, n v.numIndices, n v.numMotives, n v.numMinors, arr rs, b v.k, b v.isUnsafe]
    | .quotInfo v => pure [n (match v.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)]
  return arr (base ++ more)
def deps (ci : ConstantInfo) (iface : Bool) : List Name := Id.run do
  let mut ds := if iface && ci.isTheorem then ci.type.foldConsts {} (fun a st => st.insert a)
    else ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo v => for a in v.all ++ v.ctors do ds := ds.insert a
  | .ctorInfo v => ds := ds.insert v.induct
  | .recInfo v =>
    for a in v.all do ds := ds.insert a
    for r in v.rules do
      ds := ds.insert r.ctor
      ds := r.rhs.foldConsts ds (fun a st => st.insert a)
  | _ => pure ()
  return ds.toList

def groupNames (ci : ConstantInfo) : List Name :=
  match ci with
  | .inductInfo v => v.all
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all
  | .quotInfo _ => [`Quot, `Quot.mk, `Quot.lift, `Quot.ind]
  | .defnInfo v => if v.safety != .safe then v.all else [ci.name]
  | _ => [ci.name]

def row (ci : ConstantInfo) (mod : String) : J := Id.run do
  let ((ip, kp), st) := (do let ip ← payload ci true; let kp ← payload ci false; pure (ip, kp)).run {}
  return Json.mkObj [("event", s "constant"), ("name", s ci.name.toString), ("name_struct", nm ci.name),
    ("module", s mod), ("kind", s (kind ci)), ("nodes", .arr st.nodes),
    ("if_payload", ip), ("k_payload", kp),
    ("if_deps", toJson ((deps ci true).map Name.toString)),
    ("k_deps", toJson ((deps ci false).map Name.toString)),
    ("group_names", toJson ((groupNames ci).map Name.toString)), ("unsafe", b ci.isUnsafe), ("partial", b ci.isPartial)]
def emit (h : IO.FS.Stream) (j : J) : IO Unit := h.putStrLn j.compress

def fixtures (h : IO.FS.Stream) : IO Unit := do
  let p := mkConst `P
  let t := mkConst ``True
  let f := mkConst ``False
  for (label, body) in [("p_true", t), ("p_false", f)] do
    emit h (Json.mkObj [("event", s "fixture"), ("label", s label)])
    emit h (row (.defnInfo { name := `P, levelParams := [], type := mkSort .zero, value := body, hints := .regular 0, safety := .safe }) label)
    emit h (row (.thmInfo { name := `h, levelParams := [], type := p, value := mkConst ``True.intro }) label)
  for lps in [[`u, `v], [`v, `u]] do
    let label := if lps.head! == `u then "uv" else "vu"
    emit h (Json.mkObj [("event", s "fixture"), ("label", s label)])
    emit h (row (.axiomInfo { name := `ordered, levelParams := lps, type := mkSort (.param `u), isUnsafe := false }) label)
  for (label, proof) in [("proof_a", mkConst ``True.intro),
      ("proof_b", mkApp2 (mkConst ``id [.zero]) t (mkConst ``True.intro))] do
    emit h (Json.mkObj [("event", s "fixture"), ("label", s label)])
    emit h (row (.thmInfo { name := `proof, levelParams := [], type := t, value := proof }) label)
end B2c

def main (args : List String) : IO Unit := do
  let h ← IO.getStdout
  if args == ["--fixtures"] then B2c.fixtures h; return
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {} (loadExts := false)
  for i in [:env.header.moduleData.size] do
    let md := env.header.moduleData[i]!
    let mod := env.header.modules[i]!.module.toString
    B2c.emit h <| Json.mkObj [("event", .str "module"), ("module", .str mod),
      ("is_module", toJson md.isModule), ("imports", toJson (md.imports.map (·.module.toString))),
      ("count", toJson md.constants.size)]
    for ci in md.constants do B2c.emit h (B2c.row ci mod)
