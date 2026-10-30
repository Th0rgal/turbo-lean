/- Kernel statement material from built oleans. The host hashes this canonical,
   versioned encoding with BLAKE3; Lean's non-cryptographic Expr.hash is never used.
   This is reporting data, never a certificate that permits skipping kernel checks. -/
import Lean

open Lean
namespace TurboLean.StatementHash

private def node (tag : String) (xs : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ xs)

private def nameJson : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" #[nameJson p, toJson s]
  | .num p n => node "num" #[nameJson p, toJson n]

private def levelJson : Level → Json
  | .zero => node "zero"
  | .succ l => node "succ" #[levelJson l]
  | .max a b => node "max" #[levelJson a, levelJson b]
  | .imax a b => node "imax" #[levelJson a, levelJson b]
  | .param n => node "param" #[nameJson n]
  | .mvar n => node "mvar" #[nameJson n.name]

-- Binder display names and elaborator metadata do not affect kernel types.
private partial def exprJson : Expr → Json
  | .bvar i => node "bvar" #[toJson i]
  | .fvar n => node "fvar" #[nameJson n.name]
  | .mvar n => node "mvar" #[nameJson n.name]
  | .sort l => node "sort" #[levelJson l]
  | .const n ls => node "const" #[nameJson n, toJson (ls.map levelJson)]
  | .app f a => node "app" #[exprJson f, exprJson a]
  | .lam _ t b bi => node "lam" #[toJson (reprStr bi), exprJson t, exprJson b]
  | .forallE _ t b bi => node "forall" #[toJson (reprStr bi), exprJson t, exprJson b]
  | .letE _ t v b nd => node "let" #[exprJson t, exprJson v, exprJson b, toJson nd]
  | .lit (.natVal n) => node "nat" #[toJson n]
  | .lit (.strVal s) => node "string" #[toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => node "proj" #[nameJson n, toJson i, exprJson e]

private def hintsJson : ReducibilityHints → Json
  | .opaque => node "opaque"
  | .abbrev => node "abbrev"
  | .regular h => node "regular" #[toJson h.toNat]

private def quotJson : QuotKind → Json
  | .type => node "type"
  | .ctor => node "ctor"
  | .lift => node "lift"
  | .ind => node "ind"

private def statement (c : ConstantInfo) : Json :=
  node "statement-v1" #[toJson (c.levelParams.map nameJson), exprJson c.type]

-- Theorems contribute their type, never their proof (proof irrelevance).
-- Recursor reduction rules and inductive/constructor metadata are kernel inputs too.
private def interface (c : ConstantInfo) : Json × Array Name := Id.run do
  let mut deps := c.type.getUsedConstants
  let kind ← match c with
    | .defnInfo v =>
      deps := deps ++ v.value.getUsedConstants
      pure <| node "definition" #[exprJson v.value, hintsJson v.hints, toJson (reprStr v.safety)]
    | .opaqueInfo v =>
      deps := deps ++ v.value.getUsedConstants
      pure <| node "opaque" #[exprJson v.value, toJson v.isUnsafe]
    | .thmInfo _ => pure <| node "theorem"
    | .axiomInfo v => pure <| node "axiom" #[toJson v.isUnsafe]
    | .quotInfo v => pure <| node "quotient" #[quotJson v.kind]
    | .inductInfo v =>
      deps := deps ++ v.all.toArray ++ v.ctors.toArray
      pure <| node "inductive" #[toJson v.numParams, toJson v.numIndices,
        toJson (v.all.map nameJson), toJson (v.ctors.map nameJson),
        toJson v.numNested, toJson v.isRec, toJson v.isUnsafe, toJson v.isReflexive]
    | .ctorInfo v =>
      deps := deps.push v.induct
      pure <| node "constructor" #[nameJson v.induct, toJson v.cidx,
        toJson v.numParams, toJson v.numFields, toJson v.isUnsafe]
    | .recInfo v =>
      deps := deps ++ v.all.toArray
      for r in v.rules do
        deps := deps.push r.ctor ++ r.rhs.getUsedConstants
      pure <| node "recursor" #[toJson (v.all.map nameJson), toJson v.numParams,
        toJson v.numIndices, toJson v.numMotives, toJson v.numMinors, toJson v.k,
        toJson v.isUnsafe, toJson (v.rules.map fun r =>
          node "rule" #[nameJson r.ctor, toJson r.nfields, exprJson r.rhs])]
  return (node "interface-v1" #[statement c, kind], deps)

private def emit (j : Json) : IO Unit := do (← IO.getStdout).putStrLn j.compress

-- Import each module independently so sibling import ordering cannot perturb the dump.
def dump (mod : Name) : IO Unit := do
  let env ← importModules #[{ module := mod, importAll := true }] {} 0 #[] true false .private
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"missing module {mod}"
  let mut pending : Array Name := #[]
  for c in env.header.moduleData[idx.toNat]!.constants do
    if c.isTheorem then
      emit <| Json.mkObj [("theorem", toJson c.name.toString),
        ("statement", statement c), ("deps", toJson (c.type.getUsedConstants.map Name.toString))]
      pending := pending ++ c.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | throw <| IO.userError s!"missing constant {n}"
    let (payload, deps) := interface c
    emit <| Json.mkObj [("constant", toJson n.toString), ("interface", payload),
      ("deps", toJson (deps.map Name.toString))]
    pending := pending ++ deps
  emit <| Json.mkObj [("module", toJson mod.toString), ("complete", toJson true)]

end TurboLean.StatementHash

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  for mod in args do TurboLean.StatementHash.dump mod.toName
