/- Kernel statement material from built oleans. The host hashes this canonical,
   versioned encoding with BLAKE3; Lean's non-cryptographic Expr.hash is never used.
   This is reporting data, never a certificate that permits skipping kernel checks. -/
import Lean.Environment
import Lean.Data.Json
import Lean.Util.CollectAxioms
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.DeclarationRange

open Lean
namespace TurboLean.StatementHash

private instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

def node (tag : String) (xs : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ xs)

def nameJson (normName : Name → Name := id) : Name → Json
  | n =>
    let rec go : Name → Json
      | .anonymous => node "anonymous"
      | .str p s => node "str" #[go p, toJson s]
      | .num p k => node "num" #[go p, toJson k]
    go (normName n)

def levelJson (normName : Name → Name := id) : Level → Json
  | .zero => node "zero"
  | .succ l => node "succ" #[levelJson normName l]
  | .max a b => node "max" #[levelJson normName a, levelJson normName b]
  | .imax a b => node "imax" #[levelJson normName a, levelJson normName b]
  | .param n => node "param" #[nameJson normName n]
  | .mvar n => node "mvar" #[nameJson normName n.name]

-- Binder display names and elaborator metadata do not affect kernel types.
partial def exprJson (normName : Name → Name := id) : Expr → Json
  | .bvar i => node "bvar" #[toJson i]
  | .fvar n => node "fvar" #[nameJson normName n.name]
  | .mvar n => node "mvar" #[nameJson normName n.name]
  | .sort l => node "sort" #[levelJson normName l]
  | .const n ls => node "const" #[nameJson normName n, toJson (ls.map (levelJson normName))]
  | .app f a => node "app" #[exprJson normName f, exprJson normName a]
  | .lam _ t b bi => node "lam" #[toJson (reprStr bi), exprJson normName t, exprJson normName b]
  | .forallE _ t b bi => node "forall" #[toJson (reprStr bi), exprJson normName t, exprJson normName b]
  | .letE _ t v b nd => node "let" #[exprJson normName t, exprJson normName v, exprJson normName b, toJson nd]
  | .lit (.natVal n) => node "nat" #[toJson n]
  | .lit (.strVal s) => node "string" #[toJson s]
  | .mdata _ e => exprJson normName e
  | .proj n i e => node "proj" #[nameJson normName n, toJson i, exprJson normName e]

private def hintsJson : ReducibilityHints → Json
  | .opaque => node "opaque"
  | .abbrev => node "abbrev"
  | .regular h => node "regular" #[toJson h.toNat]

private def quotJson : QuotKind → Json
  | .type => node "type"
  | .ctor => node "ctor"
  | .lift => node "lift"
  | .ind => node "ind"

def statement (c : ConstantInfo) (normName : Name → Name := id) : Json :=
  node "statement-v1" #[toJson (c.levelParams.map (nameJson normName)), exprJson normName c.type]

def normalizeLocalPrivateName (localMod? : Option Name) (n : Name) : Name :=
  match Lean.privatePrefix? n with
  | some pfx =>
    let isLocal := match localMod? with
      | some m => pfx == Lean.mkPrivateNameCore m .anonymous || pfx == Lean.mkPrivateNameCore .anonymous .anonymous
      | none => pfx == Lean.mkPrivateNameCore .anonymous .anonymous
    if isLocal then
      Lean.mkPrivateNameCore .anonymous (Lean.privateToUserName n)
    else
      n
  | none => n

-- Theorems contribute their type, never their proof (proof irrelevance).
-- Recursor reduction rules and inductive/constructor metadata are kernel inputs too.
private def interface (c : ConstantInfo) : Json × Array Name := Id.run do
  let mut deps := c.type.getUsedConstants
  let kind ← match c with
    | .defnInfo v =>
      deps := deps ++ v.value.getUsedConstants
      pure <| node "definition" #[exprJson id v.value, hintsJson v.hints, toJson (reprStr v.safety)]
    | .opaqueInfo v =>
      deps := deps ++ v.value.getUsedConstants
      pure <| node "opaque" #[exprJson id v.value, toJson v.isUnsafe]
    | .thmInfo _ => pure <| node "theorem"
    | .axiomInfo v => pure <| node "axiom" #[toJson v.isUnsafe]
    | .quotInfo v => pure <| node "quotient" #[quotJson v.kind]
    | .inductInfo v =>
      deps := deps ++ v.all.toArray ++ v.ctors.toArray
      pure <| node "inductive" #[toJson v.numParams, toJson v.numIndices,
        toJson (v.all.map (nameJson id)), toJson (v.ctors.map (nameJson id)),
        toJson v.numNested, toJson v.isRec, toJson v.isUnsafe, toJson v.isReflexive]
    | .ctorInfo v =>
      deps := deps.push v.induct
      pure <| node "constructor" #[nameJson id v.induct, toJson v.cidx,
        toJson v.numParams, toJson v.numFields, toJson v.isUnsafe]
    | .recInfo v =>
      deps := deps ++ v.all.toArray
      for r in v.rules do
        deps := deps.push r.ctor ++ r.rhs.getUsedConstants
      pure <| node "recursor" #[toJson (v.all.map (nameJson id)), toJson v.numParams,
        toJson v.numIndices, toJson v.numMotives, toJson v.numMinors, toJson v.k,
        toJson v.isUnsafe, toJson (v.rules.map fun r =>
          node "rule" #[nameJson id r.ctor, toJson r.nfields, exprJson id r.rhs])]
  return (node "interface-v1" #[statement c, kind], deps)

private def emit (j : Json) : IO Unit := do (← IO.getStdout).putStrLn j.compress

private def isWhitelistedInitExecUnsafe (env : Environment) (idx : ModuleIdx) (c : ConstantInfo) : Bool :=
  if !c.isUnsafe then false
  else match c.value? with
    | some (.const ``Lean.enableInitializersExecution []) =>
      c.type == .app (.const ``BaseIO []) (.const ``Unit []) &&
      env.getModuleIdxFor? c.name == some idx
    | _ => false

private def isWhitelistedInitExecBridge (env : Environment) (idx : ModuleIdx) (declName : Name) : Bool :=
  if Lean.isExtern env declName then false
  else match Lean.Compiler.getImplementedBy? env declName with
    | some implName =>
      match env.find? implName, env.find? declName with
      | some implInfo, some declInfo =>
        declInfo.type == implInfo.type &&
        isWhitelistedInitExecUnsafe env idx implInfo
      | _, _ => false
    | none => false

private def safeUnsafeCallWrapperParent? (env : Environment) (idx : ModuleIdx) (c : ConstantInfo) : Option ConstantInfo :=
  let rec suffixName (nm : Name) : Option (Name × String) :=
    match nm with
    | .str p s =>
      if s.startsWith "unsafe_" && !(s.startsWith "unsafe_impl_") && (s.drop 7).toNat?.isSome then
        some (p, s)
      else
        none
    | _ => none
  if !c.isUnsafe ||
     Lean.isExtern env c.name ||
     (Lean.Compiler.getImplementedBy? env c.name).isSome ||
     env.getModuleIdxFor? c.name != some idx then
    none
  else
    match suffixName (Lean.privateToUserName c.name) with
    | some (parentUser, _) =>
      (env.header.moduleData[idx.toNat]?).bind fun mdata =>
        mdata.constants.find? fun pc =>
          pc.name != c.name &&
          !(Lean.isExtern env pc.name) &&
          (Lean.Compiler.getImplementedBy? env pc.name).isNone &&
          (pc.name == parentUser || Lean.privateToUserName pc.name == parentUser)
    | none => none

private def safeUnsafeCallWrapperBridgeParent? (env : Environment) (idx : ModuleIdx) (declName : Name) : Option ConstantInfo :=
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
          safeUnsafeCallWrapperParent? env idx implInfo
        else
          none
      | _, _ => none
    | none => none

structure AxiomMemo where
  seen   : NameMap (Array Name) := {}
  axioms : NameSet := {}

private def insertAxiomArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

private partial def collectAxiomsMemo (env : Environment) (c : Name) : StateM AxiomMemo Unit := do
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun s => { s with axioms := insertAxiomArray s.axioms axs }
    return
  let savedAxioms := s.axioms
  modify fun s => { s with axioms := {}, seen := s.seen.insert c #[] }
  let collectExpr (e : Expr) : StateM AxiomMemo Unit :=
    e.getUsedConstants.forM (collectAxiomsMemo env)
  match env.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collectAxiomsMemo env)
  | none                 => pure ()
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun s => { s with
    seen   := s.seen.insert c result
    axioms := insertAxiomArray savedAxioms result
  }

def collectAxiomsCached (env : Environment) (c : Name) (memo : AxiomMemo) : Array Name × AxiomMemo :=
  let (_, memo) := (collectAxiomsMemo env c).run { memo with axioms := {} }
  (memo.seen.find? c |>.getD #[], { memo with axioms := {} })

-- Import the union once: repeated importModules calls keep mapped olean regions alive.
-- The encoding uses constant names, never import-order-dependent module indices.
private def isAuxiliaryTheorem (env : Environment) (mod : Name) (n : Name) : Bool :=
  -- Source ranges distinguish escaped user names (e.g. «_proof_1») from auxiliaries.
  -- Strip private prefixes so private theorems remain statement-pinned.
  let sourceDeclared := (declRangeExt.find? env n <|>
    declRangeExt.find? (level := .server) env n).isSome
  let userName := Lean.privateToUserName n
  !sourceDeclared && (internal userName || match userName with
    | .str p s =>
      -- Lean 4.35 realization suffixes (Meta/{Eqns,CongrTheorems}, FunInd,
      -- PartialFixpoint/Induction, BVDecide/Normalize/Enums, CtorIdxHInj).
      -- isReservedName uses mkEqLikeNameFor's anonymous env.mainModule here.
      (env.contains p || env.contains (mkPrivateNameCore mod p)) &&
        (s ∈ ["eq_def", "eq_unfold", "congr_simp", "induct", "induct_unfolding",
          "mutual_induct", "mutual_induct_unfolding", "fun_cases", "fun_cases_unfolding",
          "fixpoint_induct", "mutual_fixpoint_induct", "partial_correctness",
          "eq_iff_enumToBitVec_eq", "enumToBitVec_le", "eq_cond_enumToBitVec", "hinj"] ||
          (s.startsWith "hcongr_" && (s.drop 7).toNat?.isSome))
    | _ => false)
where
  internal (n : Name) : Bool :=
    n.isInternalDetail || n.hasMacroScopes || match n with
      | .str p _ | .num p _ => internal p
      | .anonymous => false

def dumpWithState (env : Environment) (mod : Name) (seenInit : NameSet := {})
    (axMemoInit : AxiomMemo := {}) : IO (NameSet × AxiomMemo) := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"missing module {mod}"
  let mut pending : Array Name := #[]
  let mut unsafeDecls : Array (String × String) := #[]
  let mut unsafeInductives : Array String := #[]
  let mut implByDecls : Array (String × String) := #[]
  let mut externDecls : Array String := #[]
  let mut axiomDecls : Array String := #[]
  let mut axMemo : AxiomMemo := axMemoInit
  let mdata := env.header.moduleData[idx.toNat]!
  for c in mdata.constants do
    let (axioms, axMemoNext) := collectAxiomsCached env c.name axMemo
    axMemo := axMemoNext
    emit <| Json.mkObj [("audit", toJson c.name.toString),
      ("axioms", toJson (axioms.map Name.toString))]
    if let .axiomInfo _ := c then
      axiomDecls := axiomDecls.push c.name.toString
    if let .inductInfo iVal := c then
      if iVal.isUnsafe then
        unsafeInductives := unsafeInductives.push c.name.toString
    if c.isUnsafe && !isWhitelistedInitExecUnsafe env idx c then
      match safeUnsafeCallWrapperParent? env idx c with
      | some pc =>
        unsafeDecls := unsafeDecls.push (pc.name.toString, (Lean.privateToUserName pc.name).toString)
      | none =>
        unsafeDecls := unsafeDecls.push (c.name.toString, (Lean.privateToUserName c.name).toString)
    if Lean.isExtern env c.name then
      externDecls := externDecls.push c.name.toString
    if (Lean.Compiler.getImplementedBy? env c.name).isSome &&
       !isWhitelistedInitExecBridge env idx c.name then
      match safeUnsafeCallWrapperBridgeParent? env idx c.name with
      | some pc =>
        unsafeDecls := unsafeDecls.push (pc.name.toString, (Lean.privateToUserName pc.name).toString)
      | none =>
        implByDecls := implByDecls.push (c.name.toString, (Lean.privateToUserName c.name).toString)
    if c.isTheorem && !isAuxiliaryTheorem env mod c.name then
      emit <| Json.mkObj [("theorem", toJson c.name.toString),
        ("statement", statement c), ("deps", toJson (c.type.getUsedConstants.map Name.toString))]
      pending := pending ++ c.type.getUsedConstants
  for extraName in mdata.extraConstNames do
    if Lean.isExtern env extraName then
      externDecls := externDecls.push extraName.toString
    if (Lean.Compiler.getImplementedBy? env extraName).isSome &&
       !isWhitelistedInitExecBridge env idx extraName then
      match safeUnsafeCallWrapperBridgeParent? env idx extraName with
      | some pc =>
        unsafeDecls := unsafeDecls.push (pc.name.toString, (Lean.privateToUserName pc.name).toString)
      | none =>
        implByDecls := implByDecls.push (extraName.toString, (Lean.privateToUserName extraName).toString)
  let mut seen : NameSet := seenInit
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
  let csimp := (Compiler.CSimp.ext.ext.getModuleEntries env idx).map fun entry =>
    match entry with | .global e | .scoped _ e => e.thmName.toString
  emit <| Json.mkObj [("module", toJson mod.toString), ("complete", toJson true),
    ("csimp", toJson csimp),
    ("axiom_decls", toJson axiomDecls),
    ("unsafe_decls", toJson unsafeDecls),
    ("unsafe_inductives", toJson unsafeInductives),
    ("implemented_by", toJson implByDecls),
    ("extern_decls", toJson externDecls)]
  return (seen, axMemo)

def dump (env : Environment) (mod : Name) : IO Unit := do
  let _ ← dumpWithState env mod {} {}

end TurboLean.StatementHash

def statementHashCliMain (args : List String) : IO Unit := do
  let leanCmd := (← IO.getEnv "LEAN").getD "lean"
  initSearchPath (← findSysroot leanCmd)
  let imports : Array Import := args.toArray.map fun mod => { module := mod.toName, importAll := true }
  -- importAll + .private load .olean.server/.private too: module-header private
  -- user declarations need their ranges to override auxiliary-looking names.
  let env ← importModules imports {} 0 #[] true false .private
  let mut seen : NameSet := {}
  let mut axMemo : TurboLean.StatementHash.AxiomMemo := {}
  for mod in args do
    let (s, m) ← TurboLean.StatementHash.dumpWithState env mod.toName seen axMemo
    seen := s
    axMemo := m
