/-
  TurboLean.ConLeche (Milestone M2):
  Self-contained dependent Calculus of Inductive Constructions (CIC) kernel (`ConLeche`)
  with universe levels (`zero`, `succ`, `max`, `imax`, `param`), universe parameter
  substitution (`Level.substParams`, `Expr.instantiateLevelParams`), de Bruijn lifting &
  capture-avoiding substitution (`lift`, `subst`, `inst0`), fuel-bounded WHNF & definitional
  equality (`whnf`, `isDefEq`) with polymorphic/dependent inductive recursor $\iota$-reduction
  (`RecRule`, `applyIotaRules`), inductive typing judgment (`HasType`), bidirectional typechecker
  (`inferType`, `verifyDecl`, `verifyRecRule`), environment well-formedness (`EnvWF`, `RecRuleWF`),
  and lossless binary `.olean` declaration & recursor shard codec (`parseOleanShard`,
  `encodeOleanShard`, `parseOleanShard_encodeOleanShard_roundtrip`).
-/

namespace ConLeche

/-- Universe level in the Calculus of Inductive Constructions. -/
inductive Level where
  | zero  : Level
  | succ  : Level → Level
  | max   : Level → Level → Level
  | imax  : Level → Level → Level
  | param : String → Level
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Level

/-- Structural AST node count of a `Level`, used for lossless fuel-exact binary serialization. -/
def astSize : Level → Nat
  | .zero => 1
  | .succ u => u.astSize + 1
  | .max u v => u.astSize + v.astSize + 1
  | .imax u v => u.astSize + v.astSize + 1
  | .param _ => 1

/-- Evaluate a universe level under a default parameter assignment (`param _ ↦ 1`),
    respecting the impredicative `Prop` rule `imax u 0 = 0`. -/
def eval : Level → Nat
  | .zero => 0
  | .succ u => eval u + 1
  | .max u v => Nat.max (eval u) (eval v)
  | .imax u v =>
    let ev := eval v
    if ev == 0 then 0 else Nat.max (eval u) ev
  | .param _ => 1

/-- Check whether a universe level contains any free universe parameter `.param`. -/
def hasParam : Level → Bool
  | .zero => false
  | .succ u => hasParam u
  | .max u v => hasParam u || hasParam v
  | .imax u v => hasParam u || hasParam v
  | .param _ => true

/-- Check algebraic equivalence of two universe levels:
    either identical (`u == v`), or parameter-free with equal closed evaluation. -/
def isEquiv (u v : Level) : Bool :=
  u == v || (!hasParam u && !hasParam v && eval u == eval v)

/-- Look up universe parameter `name` in parallel lists `(params, args)`. -/
def lookupParam : List String → List Level → String → Level
  | p :: ps, a :: as, name => if p == name then a else lookupParam ps as name
  | _, _, name => .param name

/-- Substitute universe parameters `params` with universe arguments `args` in a `Level`. -/
def substParams (params : List String) (args : List Level) : Level → Level
  | .zero => .zero
  | .succ u => .succ (substParams params args u)
  | .max u v => .max (substParams params args u) (substParams params args v)
  | .imax u v => .imax (substParams params args u) (substParams params args v)
  | .param s => lookupParam params args s

/-- Substituting an empty universe parameter list leaves any universe level `u` unchanged. -/
theorem substParams_nil (u : Level) :
    substParams [] [] u = u := by
  induction u with
  | zero => rfl
  | succ u ih => dsimp [substParams]; rw [ih]
  | max u v ihu ihv => dsimp [substParams]; rw [ihu, ihv]
  | imax u v ihu ihv => dsimp [substParams]; rw [ihu, ihv]
  | param _ => rfl

end Level

/-- Core dependent CIC expression AST using de Bruijn indices for bound variables. -/
inductive Expr where
  | bvar    : Nat → Expr
  | sort    : Level → Expr
  | const   : String → List Level → Expr
  | app     : Expr → Expr → Expr
  | lam     : Expr → Expr → Expr
  | forallE : Expr → Expr → Expr
  | letE    : Expr → Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Expr

/-- Structural AST node count of an `Expr`, used for lossless fuel-exact binary serialization. -/
def astSize : Expr → Nat
  | .bvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app fn a => fn.astSize + a.astSize + 1
  | .lam dom body => dom.astSize + body.astSize + 1
  | .forallE dom body => dom.astSize + body.astSize + 1
  | .letE ty val body => ty.astSize + val.astSize + body.astSize + 1

/-- Shift free de Bruijn indices `≥ cutoff` by `delta`. -/
def lift (delta cutoff : Nat) : Expr → Expr
  | .bvar idx => if idx >= cutoff then .bvar (idx + delta) else .bvar idx
  | .sort u => .sort u
  | .const name lvls => .const name lvls
  | .app fn arg => .app (lift delta cutoff fn) (lift delta cutoff arg)
  | .lam dom body => .lam (lift delta cutoff dom) (lift delta (cutoff + 1) body)
  | .forallE dom body => .forallE (lift delta cutoff dom) (lift delta (cutoff + 1) body)
  | .letE ty val body =>
    .letE (lift delta cutoff ty) (lift delta cutoff val) (lift delta (cutoff + 1) body)

/-- Lifting by `0` at any `cutoff` is the identity on all expressions (`lift 0 cutoff e = e`). -/
theorem lift_zero (cutoff : Nat) (e : Expr) :
    lift 0 cutoff e = e := by
  induction e generalizing cutoff with
  | bvar idx =>
    dsimp [lift]
    split <;> rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app fn a ihf iha => dsimp [lift]; rw [ihf cutoff, iha cutoff]
  | lam dom body ihd ihb => dsimp [lift]; rw [ihd cutoff, ihb (cutoff + 1)]
  | forallE dom body ihd ihb => dsimp [lift]; rw [ihd cutoff, ihb (cutoff + 1)]
  | letE ty val body iht ihv ihb => dsimp [lift]; rw [iht cutoff, ihv cutoff, ihb (cutoff + 1)]

/-- Substitute `arg` for de Bruijn index `depth` and decrement free indices `> depth`. -/
def subst (depth : Nat) (arg : Expr) : Expr → Expr
  | .bvar idx =>
    if idx == depth then lift depth 0 arg
    else if idx > depth then .bvar (idx - 1)
    else .bvar idx
  | .sort u => .sort u
  | .const name lvls => .const name lvls
  | .app fn a => .app (subst depth arg fn) (subst depth arg a)
  | .lam dom body => .lam (subst depth arg dom) (subst (depth + 1) arg body)
  | .forallE dom body => .forallE (subst depth arg dom) (subst (depth + 1) arg body)
  | .letE ty val body =>
    .letE (subst depth arg ty) (subst depth arg val) (subst (depth + 1) arg body)

/-- Instantiate de Bruijn variable `0` with `arg`. -/
def inst0 (arg : Expr) (body : Expr) : Expr :=
  subst 0 arg body

/-- Instantiating variable `0` in `.bvar 0` with any expression `arg` (closed or open) returns `arg` unchanged. -/
theorem inst0_bvar0 (arg : Expr) :
    inst0 arg (.bvar 0) = arg := by
  dsimp [inst0, subst]
  exact lift_zero 0 arg

/-- De Bruijn cancellation lemma (`subst_lift1`):
    substituting `arg` at `depth` after lifting free indices `≥ depth` by `1` is the identity. -/
theorem subst_lift1 (depth : Nat) (arg : Expr) (e : Expr) :
    subst depth arg (lift 1 depth e) = e := by
  induction e generalizing depth with
  | bvar idx =>
    dsimp [lift]
    split
    · rename_i hge
      dsimp [subst]
      have hne : (idx + 1 == depth) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      have hgt : idx + 1 > depth := by omega
      simp [hne, hgt]
    · rename_i hlt
      dsimp [subst]
      have hne : (idx == depth) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      have hngt : ¬(idx > depth) := by omega
      simp [hne, hngt]
  | sort _ => rfl
  | const _ _ => rfl
  | app fn a ihf iha =>
    dsimp [lift, subst]
    rw [ihf depth, iha depth]
  | lam dom body ihd ihb =>
    dsimp [lift, subst]
    rw [ihd depth, ihb (depth + 1)]
  | forallE dom body ihd ihb =>
    dsimp [lift, subst]
    rw [ihd depth, ihb (depth + 1)]
  | letE ty val body iht ihv ihb =>
    dsimp [lift, subst]
    rw [iht depth, ihv depth, ihb (depth + 1)]

/-- Non-dependent binder instantiation (`inst0_lift1`):
    instantiating variable `0` in a term lifted by `1` at cutoff `0` returns the term unchanged. -/
theorem inst0_lift1 (arg ty : Expr) :
    inst0 arg (lift 1 0 ty) = ty :=
  subst_lift1 0 arg ty

/-- Substitute universe parameters `params` with universe arguments `args` throughout an `Expr`. -/
def instantiateLevelParams (params : List String) (args : List Level) : Expr → Expr
  | .bvar idx => .bvar idx
  | .sort u => .sort (Level.substParams params args u)
  | .const name lvls => .const name (lvls.map (Level.substParams params args))
  | .app fn arg => .app (instantiateLevelParams params args fn) (instantiateLevelParams params args arg)
  | .lam dom body => .lam (instantiateLevelParams params args dom) (instantiateLevelParams params args body)
  | .forallE dom body => .forallE (instantiateLevelParams params args dom) (instantiateLevelParams params args body)
  | .letE ty val body =>
    .letE (instantiateLevelParams params args ty)
          (instantiateLevelParams params args val)
          (instantiateLevelParams params args body)

/-- Instantiating an empty universe parameter list leaves any expression `e` unchanged. -/
theorem instantiateLevelParams_nil (e : Expr) :
    instantiateLevelParams [] [] e = e := by
  induction e with
  | bvar _ => rfl
  | sort u => dsimp [instantiateLevelParams]; rw [Level.substParams_nil]
  | const name lvls =>
    dsimp [instantiateLevelParams]
    congr 1
    induction lvls with
    | nil => rfl
    | cons l ls ih => dsimp [List.map]; rw [Level.substParams_nil, ih]
  | app fn a ihf iha => dsimp [instantiateLevelParams]; rw [ihf, iha]
  | lam dom body ihd ihb => dsimp [instantiateLevelParams]; rw [ihd, ihb]
  | forallE dom body ihd ihb => dsimp [instantiateLevelParams]; rw [ihd, ihb]
  | letE ty val body iht ihv ihb => dsimp [instantiateLevelParams]; rw [iht, ihv, ihb]

end Expr

/-- Kernel declaration entry in a `ConLeche` environment, including universe parameter list `levelParams`. -/
structure Decl where
  name        : String
  levelParams : List String := []
  ty          : Expr
  val         : Expr
  wfTag       : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Universe-polymorphic recursor computation rule ($\iota$-reduction) for an inductive constructor `ctorName`
    of inductive type `indTy` eliminated by `recName`, reducing
    `.app (.const recName lvls) (.app (.const ctorName lvls) arg)` to
    `.app (Expr.instantiateLevelParams levelParams lvls rhsTemplate) arg`. -/
structure RecRule where
  recName     : String
  ctorName    : String
  levelParams : List String := []
  rhsTemplate : Expr
  argDom      : Expr
  indTy       : Expr := .sort .zero
  resultCod   : Expr
  isDependent : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

namespace RecRule

/-- Expected constructor type `∀ (_ : argDomInst), indTyInst` at universe instantiation `lvls`. -/
def ctorExpectedInst (rule : RecRule) (lvls : List Level) : Expr :=
  let argDomInst := Expr.instantiateLevelParams rule.levelParams lvls rule.argDom
  let indTyInst  := Expr.instantiateLevelParams rule.levelParams lvls rule.indTy
  .forallE argDomInst (Expr.lift 1 0 indTyInst)

/-- Expected recursor type at universe instantiation `lvls`:
    - non-dependent (`isDependent = false`): `∀ (_ : indTyInst), resCodInst`
    - dependent (`isDependent = true`, where `resultCod` is the motive `M`): `∀ (x : indTyInst), M x` -/
def recExpectedInst (rule : RecRule) (lvls : List Level) : Expr :=
  let indTyInst  := Expr.instantiateLevelParams rule.levelParams lvls rule.indTy
  let resCodInst := Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod
  if rule.isDependent then
    .forallE indTyInst (.app (Expr.lift 1 0 resCodInst) (.bvar 0))
  else
    .forallE indTyInst (Expr.lift 1 0 resCodInst)

/-- Expected RHS template type at universe instantiation `lvls`:
    - non-dependent (`isDependent = false`): `∀ (_ : argDomInst), resCodInst`
    - dependent (`isDependent = true`, where `resultCod` is the motive `M`): `∀ (p : argDomInst), M (ctor p)` -/
def rhsExpectedInst (rule : RecRule) (lvls : List Level) : Expr :=
  let argDomInst := Expr.instantiateLevelParams rule.levelParams lvls rule.argDom
  let resCodInst := Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod
  if rule.isDependent then
    .forallE argDomInst (.app (Expr.lift 1 0 resCodInst) (.app (.const rule.ctorName lvls) (.bvar 0)))
  else
    .forallE argDomInst (Expr.lift 1 0 resCodInst)

/-- Instantiated result type of eliminating `.app (.const rule.ctorName lvls) payload`:
    - non-dependent (`isDependent = false`): `resCodInst`
    - dependent (`isDependent = true`): `.app resCodInst (.app (.const rule.ctorName lvls) payload)` -/
def iotaResultTy (rule : RecRule) (lvls : List Level) (payload : Expr) : Expr :=
  let resCodInst := Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod
  if rule.isDependent then
    .app resCodInst (.app (.const rule.ctorName lvls) payload)
  else
    resCodInst

end RecRule

/-- Apply a single recursor $\iota$-reduction rule `rule` to an elimination spine `e`,
    checking universe parameter arity and instantiating `rule.rhsTemplate` with `rLvls`. -/
def evalIotaStep (rule : RecRule) (e : Expr) : Option Expr :=
  match e with
  | .app (.const rName rLvls) (.app (.const cName cLvls) payload) =>
    if rName == rule.recName && cName == rule.ctorName &&
       decide (rLvls = cLvls) && rule.levelParams.length == rLvls.length then
      some (.app (Expr.instantiateLevelParams rule.levelParams rLvls rule.rhsTemplate) payload)
    else
      none
  | _ => none

/-- Search a list of verified recursor rules `rules` for an applicable $\iota$-reduction step on `e`. -/
def applyIotaRules : List RecRule → Expr → Option Expr
  | [], _ => none
  | r :: rest, e =>
    match evalIotaStep r e with
    | some red => some red
    | none => applyIotaRules rest e

/-- Kernel environment holding verified declarations, inductive recursor $\iota$-rules, and `.olean` shard header metadata. -/
structure Env where
  decls       : List Decl
  recRules    : List RecRule := []
  headerMagic : UInt32 := 0x4F4C454E
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Env

/-- Look up a declaration by name in `env`. -/
def lookup? (env : Env) (name : String) : Option Decl :=
  env.decls.find? (fun d => d.name == name)

end Env

/-- Fuel-bounded Weak Head Normal Form (WHNF) evaluator supporting $\beta$-reduction,
    $\zeta$-reduction (`letE`), $\delta$-unfolding of verified environment constants
    with universe parameter instantiation (`Expr.instantiateLevelParams`),
    and $\iota$-reduction via `env.recRules`. -/
def whnf (fuel : Nat) (env : Env) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match e with
    | .app fn arg =>
      match applyIotaRules env.recRules (.app fn arg) with
      | some red => whnf fuel' env red
      | none =>
        let fn' := whnf fuel' env fn
        match fn' with
        | .lam _ body => whnf fuel' env (Expr.inst0 arg body)
        | .const rName _ =>
          if env.recRules.any (fun r => r.recName == rName) then
            let arg' := whnf fuel' env arg
            match applyIotaRules env.recRules (.app fn' arg') with
            | some red => whnf fuel' env red
            | none => .app fn' arg
          else
            .app fn' arg
        | _ => .app fn' arg
    | .letE _ val body =>
      whnf fuel' env (Expr.inst0 val body)
    | .const name lvls =>
      match env.lookup? name with
      | some d =>
        if d.wfTag && d.levelParams.length == lvls.length then
          whnf fuel' env (Expr.instantiateLevelParams d.levelParams lvls d.val)
        else
          e
      | none => e
    | _ => e

/-- Fuel-bounded definitional equality (`isDefEq`) combining syntactic equality,
    WHNF $\beta\delta\zeta\iota$-reduction, and structural recursion under binders. -/
def isDefEq (fuel : Nat) (env : Env) (a b : Expr) : Bool :=
  if decide (a = b) then true
  else
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let a' := whnf fuel' env a
      let b' := whnf fuel' env b
      if decide (a' = b') || decide (a' = b) || decide (a = b') then true
      else
        match a', b' with
        | .sort u, .sort v => Level.isEquiv u v
        | .app f1 x1, .app f2 x2 =>
          isDefEq fuel' env f1 f2 && isDefEq fuel' env x1 x2
        | .lam d1 body1, .lam d2 body2 =>
          isDefEq fuel' env d1 d2 && isDefEq fuel' env body1 body2
        | .forallE d1 body1, .forallE d2 body2 =>
          isDefEq fuel' env d1 d2 && isDefEq fuel' env body1 body2
        | .letE t1 v1 body1, .letE t2 v2 body2 =>
          isDefEq fuel' env t1 t2 && isDefEq fuel' env v1 v2 && isDefEq fuel' env body1 body2
        | _, _ => false

/-- Inductive dependent CIC typing judgment `HasType env ctx e ty` ($\Sigma; \Gamma \vdash e : \tau$). -/
inductive HasType (env : Env) : List Expr → Expr → Expr → Prop where
  | bvar {ctx : List Expr} {idx : Nat} {ty : Expr} :
      ctx[idx]? = some ty →
      HasType env ctx (.bvar idx) (Expr.lift (idx + 1) 0 ty)
  | sort {ctx : List Expr} (u : Level) :
      HasType env ctx (.sort u) (.sort (.succ u))
  | const {ctx : List Expr} {name : String} {lvls : List Level} {d : Decl} :
      env.lookup? name = some d →
      d.wfTag = true →
      (d.levelParams.length == lvls.length) = true →
      HasType env ctx (.const name lvls) (Expr.instantiateLevelParams d.levelParams lvls d.ty)
  | app {ctx : List Expr} {fn arg dom body : Expr} :
      HasType env ctx fn (.forallE dom body) →
      HasType env ctx arg dom →
      HasType env ctx (.app fn arg) (Expr.inst0 arg body)
  | lam {ctx : List Expr} {dom body bodyTy : Expr} {u : Level} :
      HasType env ctx dom (.sort u) →
      HasType env (dom :: ctx) body bodyTy →
      HasType env ctx (.lam dom body) (.forallE dom bodyTy)
  | forallE {ctx : List Expr} {dom body : Expr} {u v : Level} :
      HasType env ctx dom (.sort u) →
      HasType env (dom :: ctx) body (.sort v) →
      HasType env ctx (.forallE dom body) (.sort (.imax u v))
  | letE {ctx : List Expr} {ty val body bodyTy : Expr} {u : Level} :
      HasType env ctx ty (.sort u) →
      HasType env ctx val ty →
      HasType env (ty :: ctx) body bodyTy →
      HasType env ctx (.letE ty val body) (Expr.inst0 val bodyTy)
  | conv {ctx : List Expr} {e tyA tyB : Expr} {u : Level} :
      HasType env ctx e tyA →
      HasType env ctx tyB (.sort u) →
      isDefEq 64 env tyA tyB = true →
      HasType env ctx e tyB

/-- Bidirectional dependent CIC type inference (`inferType fuel env ctx e`). -/
def inferType : Nat → Env → List Expr → Expr → Option Expr
  | 0, _, _, _ => none
  | _ + 1, _, ctx, .bvar idx =>
    match ctx[idx]? with
    | some ty => some (Expr.lift (idx + 1) 0 ty)
    | none => none
  | _ + 1, _, _, .sort u =>
    some (.sort (.succ u))
  | _ + 1, env, _, .const name lvls =>
    match env.lookup? name with
    | some d =>
      if d.wfTag && d.levelParams.length == lvls.length then
        some (Expr.instantiateLevelParams d.levelParams lvls d.ty)
      else none
    | none => none
  | fuel + 1, env, ctx, .app fn arg =>
    match inferType fuel env ctx fn, inferType fuel env ctx arg with
    | some (.forallE dom body), some argTy =>
      if decide (argTy = dom) then some (Expr.inst0 arg body) else none
    | _, _ => none
  | fuel + 1, env, ctx, .lam dom body =>
    match inferType fuel env ctx dom, inferType fuel env (dom :: ctx) body with
    | some (.sort _), some bodyTy => some (.forallE dom bodyTy)
    | _, _ => none
  | fuel + 1, env, ctx, .forallE dom body =>
    match inferType fuel env ctx dom, inferType fuel env (dom :: ctx) body with
    | some (.sort u), some (.sort v) => some (.sort (.imax u v))
    | _, _ => none
  | fuel + 1, env, ctx, .letE ty val body =>
    match inferType fuel env ctx ty, inferType fuel env ctx val, inferType fuel env (ty :: ctx) body with
    | some (.sort _), some valTy, some bodyTy =>
      if decide (valTy = ty) then some (Expr.inst0 val bodyTy) else none
    | _, _, _ => none

/-- Semantic CIC validity predicate for a kernel declaration `d` in `env`:
    `d` is well-founded (`d.wfTag = true`), its type `d.ty` is a valid sort (`∃ u, HasType env [] d.ty (.sort u)`),
    and its value `d.val` has type `d.ty` (`HasType env [] d.val d.ty`). -/
def CICValid (env : Env) (d : Decl) : Prop :=
  d.wfTag = true ∧
  (∃ u : Level, HasType env [] d.ty (.sort u)) ∧
  HasType env [] d.val d.ty

/-- Computable kernel declaration verifier (`verifyDecl`):
    checks `d.wfTag`, infers `d.ty : .sort u` and `d.val : valTy`, and verifies
    definitional equality `isDefEq 64 env valTy d.ty`. -/
def verifyDecl (env : Env) (d : Decl) : Bool :=
  d.wfTag &&
  match inferType 64 env [] d.ty, inferType 64 env [] d.val with
  | some (.sort _), some valTy => isDefEq 64 env valTy d.ty
  | _, _ => false

/-- Well-formedness predicate for a universe-polymorphic inductive recursor $\iota$-reduction rule `rule` in `env`
    at universe instantiation `lvls` (supporting both non-dependent `isDependent = false` and dependent
    motive `isDependent = true` rules via `rule.recExpectedInst` and `rule.rhsExpectedInst`). -/
def RecRuleInstWF (env : Env) (ctx : List Expr) (rule : RecRule) (lvls : List Level) : Prop :=
  let rhsInst := Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate
  (rule.levelParams.length == lvls.length) = true ∧
  HasType env ctx (.const rule.ctorName lvls) (rule.ctorExpectedInst lvls) ∧
  HasType env ctx (.const rule.recName lvls) (rule.recExpectedInst lvls) ∧
  HasType env ctx rhsInst (rule.rhsExpectedInst lvls)

/-- Closed canonical well-formedness predicate for `rule` in `env` at its generic universe parameter vector
    `lvls := rule.levelParams.map Level.param`. -/
def RecRuleWF (env : Env) (rule : RecRule) : Prop :=
  RecRuleInstWF env [] rule (rule.levelParams.map Level.param)

/-- Computable kernel verifier for an inductive recursor $\iota$-reduction rule `rule` in `env`
    at typing context `ctx` and universe instantiation `lvls` (supporting both non-dependent and
    dependent-motive rules). -/
def verifyRecRuleInst (env : Env) (ctx : List Expr) (rule : RecRule) (lvls : List Level) : Bool :=
  (rule.levelParams.length == lvls.length) &&
  let rhsInst := Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate
  match inferType 64 env ctx (.const rule.ctorName lvls),
        inferType 64 env ctx (.const rule.recName lvls),
        inferType 64 env ctx rhsInst with
  | some ctorTy, some recTy, some rhsTy =>
    decide (ctorTy = rule.ctorExpectedInst lvls) &&
    decide (recTy = rule.recExpectedInst lvls) &&
    decide (rhsTy = rule.rhsExpectedInst lvls)
  | _, _, _ => false

/-- Computable kernel verifier for an inductive recursor $\iota$-reduction rule `rule` in `env`
    at its canonical universe parameter instantiation `rule.levelParams.map Level.param`. -/
def verifyRecRule (env : Env) (rule : RecRule) : Bool :=
  verifyRecRuleInst env [] rule (rule.levelParams.map Level.param)

/-! ## Lossless Binary `.olean` Declaration & Recursor Shard Codec (`OLEN` v1) -/

/-- Losslessly encode an arbitrary `Nat` as a self-delimiting unary-prefixed byte stream. -/
def encodeNat : Nat → List UInt8
  | 0 => [0]
  | n + 1 => 1 :: encodeNat n

/-- Decode a self-delimiting `Nat` from `stream`, returning `(n, rest)`. -/
def decodeNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if b == 0 then
      some (0, rest)
    else if b == 1 then
      match decodeNat rest with
      | some (n, rest') => some (n + 1, rest')
      | none => none
    else
      none

/-- Round-trip theorem for `encodeNat`/`decodeNat` on arbitrary `n : Nat` (no 255 bound). -/
theorem decodeNat_encodeNat (n : Nat) (rest : List UInt8) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    dsimp [encodeNat, decodeNat]
    rw [ih]

/-- Extract exactly `n` bytes from the front of a byte stream `stream`. -/
def takeExactBytes : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, rest => some ([], rest)
  | _ + 1, [] => none
  | n + 1, b :: rest =>
    match takeExactBytes n rest with
    | some (xs, tail) => some (b :: xs, tail)
    | none => none

/-- Round-trip theorem for `takeExactBytes` on arbitrary byte list `bs`. -/
theorem takeExactBytes_append (bs rest : List UInt8) :
    takeExactBytes bs.length (bs ++ rest) = some (bs, rest) := by
  induction bs with
  | nil => rfl
  | cons b bs' ih =>
    dsimp [List.length, takeExactBytes]
    rw [ih]

/-- Losslessly encode an arbitrary-length UTF-8 `String` into a byte stream. -/
def encodeStringStream (s : String) : List UInt8 :=
  let bs := s.toUTF8.data.toList
  encodeNat bs.length ++ bs

/-- Decode an arbitrary-length UTF-8 `String` from `stream`. -/
def decodeStringStream (stream : List UInt8) : Option (String × List UInt8) :=
  match decodeNat stream with
  | none => none
  | some (len, rest1) =>
    match takeExactBytes len rest1 with
    | none => none
    | some (bs, rest2) =>
      match String.fromUTF8? (ByteArray.mk bs.toArray) with
      | some s => some (s, rest2)
      | none => none

/-- Round-trip theorem for `encodeStringStream`/`decodeStringStream` on arbitrary UTF-8 strings. -/
theorem decodeStringStream_encodeStringStream (s : String) (rest : List UInt8) :
    decodeStringStream (encodeStringStream s ++ rest) = some (s, rest) := by
  unfold encodeStringStream decodeStringStream
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  rw [takeExactBytes_append]
  dsimp only
  have hba : ByteArray.mk s.toUTF8.data.toList.toArray = s.toUTF8 := by
    rcases h : s.toUTF8 with ⟨arr⟩
    simp
  rw [hba]
  have hs : String.fromUTF8? s.toUTF8 = some s := by
    rcases s with ⟨ba, h⟩
    simp [String.toUTF8, String.fromUTF8?, String.fromUTF8, h]
  rw [hs]

/-- Encode a list of strings (`levelParams`) without length truncation. -/
def encodeStringListAux : List String → List UInt8
  | [] => []
  | s :: rest => encodeStringStream s ++ encodeStringListAux rest

/-- Decode `count` strings from `stream`. -/
def decodeStringListAux : Nat → List UInt8 → Option (List String × List UInt8)
  | 0, rest => some ([], rest)
  | count + 1, stream =>
    match decodeStringStream stream with
    | some (s, rest1) =>
      match decodeStringListAux count rest1 with
      | some (ss, rest2) => some (s :: ss, rest2)
      | none => none
    | none => none

theorem decodeStringListAux_encode (ss : List String) (rest : List UInt8) :
    decodeStringListAux ss.length (encodeStringListAux ss ++ rest) = some (ss, rest) := by
  induction ss generalizing rest with
  | nil => rfl
  | cons s ss' ih =>
    dsimp [List.length, encodeStringListAux, decodeStringListAux]
    rw [List.append_assoc, decodeStringStream_encodeStringStream]
    dsimp only
    rw [ih rest]

/-- Losslessly encode a `List String` with an unbounded `encodeNat` count prefix. -/
def encodeStringList (ss : List String) : List UInt8 :=
  encodeNat ss.length ++ encodeStringListAux ss

/-- Decode a `List String` from `stream`. -/
def decodeStringList (stream : List UInt8) : Option (List String × List UInt8) :=
  match decodeNat stream with
  | some (n, rest1) => decodeStringListAux n rest1
  | none => none

theorem decodeStringList_encodeStringList (ss : List String) (rest : List UInt8) :
    decodeStringList (encodeStringList ss ++ rest) = some (ss, rest) := by
  unfold encodeStringList decodeStringList
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  exact decodeStringListAux_encode ss rest

/-- Encode a `Level` AST body into tag-prefixed bytes. -/
def encodeOleanLevelAux : Level → List UInt8
  | .zero => [0]
  | .succ u => 1 :: encodeOleanLevelAux u
  | .max u v => 2 :: (encodeOleanLevelAux u ++ encodeOleanLevelAux v)
  | .imax u v => 3 :: (encodeOleanLevelAux u ++ encodeOleanLevelAux v)
  | .param s => 4 :: encodeStringStream s

/-- Decode a `Level` AST body with explicit recursion `fuel`. -/
def decodeOleanLevelAux : Nat → List UInt8 → Option (Level × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel' + 1, tag :: rest =>
    if tag == 0 then some (.zero, rest)
    else if tag == 1 then
      match decodeOleanLevelAux fuel' rest with
      | some (u, rest1) => some (.succ u, rest1)
      | none => none
    else if tag == 2 then
      match decodeOleanLevelAux fuel' rest with
      | some (u, rest1) =>
        match decodeOleanLevelAux fuel' rest1 with
        | some (v, rest2) => some (.max u v, rest2)
        | none => none
      | none => none
    else if tag == 3 then
      match decodeOleanLevelAux fuel' rest with
      | some (u, rest1) =>
        match decodeOleanLevelAux fuel' rest1 with
        | some (v, rest2) => some (.imax u v, rest2)
        | none => none
      | none => none
    else if tag == 4 then
      match decodeStringStream rest with
      | some (s, rest1) => some (.param s, rest1)
      | none => none
    else none

theorem decodeOleanLevelAux_encode (u : Level) (fuel : Nat) (rest : List UInt8)
    (hfuel : u.astSize ≤ fuel) :
    decodeOleanLevelAux fuel (encodeOleanLevelAux u ++ rest) = some (u, rest) := by
  induction u generalizing fuel rest with
  | zero =>
    cases fuel with
    | zero => simp [Level.astSize] at hfuel
    | succ f => rfl
  | succ u ih =>
    cases fuel with
    | zero => simp [Level.astSize] at hfuel
    | succ f =>
      have hf : u.astSize ≤ f := by simp [Level.astSize] at hfuel; omega
      dsimp [encodeOleanLevelAux, decodeOleanLevelAux]
      rw [ih f rest hf]
  | max u v ihu ihv =>
    cases fuel with
    | zero => simp [Level.astSize] at hfuel
    | succ f =>
      have hfu : u.astSize ≤ f := by simp [Level.astSize] at hfuel; omega
      have hfv : v.astSize ≤ f := by simp [Level.astSize] at hfuel; omega
      dsimp [encodeOleanLevelAux, decodeOleanLevelAux]
      rw [List.append_assoc, ihu f (encodeOleanLevelAux v ++ rest) hfu]
      dsimp only
      rw [ihv f rest hfv]
  | imax u v ihu ihv =>
    cases fuel with
    | zero => simp [Level.astSize] at hfuel
    | succ f =>
      have hfu : u.astSize ≤ f := by simp [Level.astSize] at hfuel; omega
      have hfv : v.astSize ≤ f := by simp [Level.astSize] at hfuel; omega
      dsimp [encodeOleanLevelAux, decodeOleanLevelAux]
      rw [List.append_assoc, ihu f (encodeOleanLevelAux v ++ rest) hfu]
      dsimp only
      rw [ihv f rest hfv]
  | param s =>
    cases fuel with
    | zero => simp [Level.astSize] at hfuel
    | succ f =>
      dsimp [encodeOleanLevelAux, decodeOleanLevelAux]
      rw [decodeStringStream_encodeStringStream]

/-- Losslessly encode a `ConLeche.Level` prefixed by its exact structural fuel `u.astSize`. -/
def encodeOleanLevel (u : Level) : List UInt8 :=
  encodeNat u.astSize ++ encodeOleanLevelAux u

/-- Decode a `ConLeche.Level` from `stream` without any fixed depth cap. -/
def decodeOleanLevelStream (stream : List UInt8) : Option (Level × List UInt8) :=
  match decodeNat stream with
  | some (fuel, rest1) => decodeOleanLevelAux fuel rest1
  | none => none

/-- Unconditional round-trip theorem for `encodeOleanLevel`/`decodeOleanLevelStream`. -/
theorem decodeOleanLevelStream_encodeOleanLevel (u : Level) (rest : List UInt8) :
    decodeOleanLevelStream (encodeOleanLevel u ++ rest) = some (u, rest) := by
  unfold encodeOleanLevel decodeOleanLevelStream
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  exact decodeOleanLevelAux_encode u u.astSize rest (Nat.le_refl _)

/-- Encode a list of universe levels without count truncation. -/
def encodeOleanLevelsAux : List Level → List UInt8
  | [] => []
  | l :: rest => encodeOleanLevel l ++ encodeOleanLevelsAux rest

/-- Decode `count` universe levels from `stream`. -/
def decodeOleanLevelsAux : Nat → List UInt8 → Option (List Level × List UInt8)
  | 0, rest => some ([], rest)
  | count + 1, stream =>
    match decodeOleanLevelStream stream with
    | some (l, rest1) =>
      match decodeOleanLevelsAux count rest1 with
      | some (ls, rest2) => some (l :: ls, rest2)
      | none => none
    | none => none

theorem decodeOleanLevelsAux_encode (ls : List Level) (rest : List UInt8) :
    decodeOleanLevelsAux ls.length (encodeOleanLevelsAux ls ++ rest) = some (ls, rest) := by
  induction ls generalizing rest with
  | nil => rfl
  | cons l ls' ih =>
    dsimp [List.length, encodeOleanLevelsAux, decodeOleanLevelsAux]
    rw [List.append_assoc, decodeOleanLevelStream_encodeOleanLevel]
    dsimp only
    rw [ih rest]

/-- Losslessly encode `List Level` with an unbounded `encodeNat` count prefix. -/
def encodeOleanLevels (ls : List Level) : List UInt8 :=
  encodeNat ls.length ++ encodeOleanLevelsAux ls

/-- Decode `List Level` from `stream`. -/
def decodeOleanLevelsStream (stream : List UInt8) : Option (List Level × List UInt8) :=
  match decodeNat stream with
  | some (n, rest1) => decodeOleanLevelsAux n rest1
  | none => none

theorem decodeOleanLevelsStream_encodeOleanLevels (ls : List Level) (rest : List UInt8) :
    decodeOleanLevelsStream (encodeOleanLevels ls ++ rest) = some (ls, rest) := by
  unfold encodeOleanLevels decodeOleanLevelsStream
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  exact decodeOleanLevelsAux_encode ls rest

/-- Encode a `ConLeche.Expr` body into tag-prefixed bytes using `encodeNat` for `.bvar` indices. -/
def encodeOleanExprAux : Expr → List UInt8
  | .bvar idx => 0 :: encodeNat idx
  | .sort u => 1 :: encodeOleanLevel u
  | .const name lvls => 2 :: (encodeStringStream name ++ encodeOleanLevels lvls)
  | .app fn a => 3 :: (encodeOleanExprAux fn ++ encodeOleanExprAux a)
  | .lam dom body => 4 :: (encodeOleanExprAux dom ++ encodeOleanExprAux body)
  | .forallE dom body => 5 :: (encodeOleanExprAux dom ++ encodeOleanExprAux body)
  | .letE ty val body => 6 :: (encodeOleanExprAux ty ++ encodeOleanExprAux val ++ encodeOleanExprAux body)

/-- Decode a `ConLeche.Expr` body with explicit recursion `fuel`. -/
def decodeOleanExprAux : Nat → List UInt8 → Option (Expr × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel' + 1, tag :: rest =>
    if tag == 0 then
      match decodeNat rest with
      | some (idx, rest1) => some (.bvar idx, rest1)
      | none => none
    else if tag == 1 then
      match decodeOleanLevelStream rest with
      | some (u, rest1) => some (.sort u, rest1)
      | none => none
    else if tag == 2 then
      match decodeStringStream rest with
      | some (name, rest1) =>
        match decodeOleanLevelsStream rest1 with
        | some (lvls, rest2) => some (.const name lvls, rest2)
        | none => none
      | none => none
    else if tag == 3 then
      match decodeOleanExprAux fuel' rest with
      | some (fn, rest1) =>
        match decodeOleanExprAux fuel' rest1 with
        | some (a, rest2) => some (.app fn a, rest2)
        | none => none
      | none => none
    else if tag == 4 then
      match decodeOleanExprAux fuel' rest with
      | some (dom, rest1) =>
        match decodeOleanExprAux fuel' rest1 with
        | some (body, rest2) => some (.lam dom body, rest2)
        | none => none
      | none => none
    else if tag == 5 then
      match decodeOleanExprAux fuel' rest with
      | some (dom, rest1) =>
        match decodeOleanExprAux fuel' rest1 with
        | some (body, rest2) => some (.forallE dom body, rest2)
        | none => none
      | none => none
    else if tag == 6 then
      match decodeOleanExprAux fuel' rest with
      | some (ty, rest1) =>
        match decodeOleanExprAux fuel' rest1 with
        | some (val, rest2) =>
          match decodeOleanExprAux fuel' rest2 with
          | some (body, rest3) => some (.letE ty val body, rest3)
          | none => none
        | none => none
      | none => none
    else none

theorem decodeOleanExprAux_encode (e : Expr) (fuel : Nat) (rest : List UInt8)
    (hfuel : e.astSize ≤ fuel) :
    decodeOleanExprAux fuel (encodeOleanExprAux e ++ rest) = some (e, rest) := by
  induction e generalizing fuel rest with
  | bvar idx =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [decodeNat_encodeNat]
  | sort u =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [decodeOleanLevelStream_encodeOleanLevel]
  | const name lvls =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [List.append_assoc, decodeStringStream_encodeStringStream]
      dsimp only
      rw [decodeOleanLevelsStream_encodeOleanLevels]
  | app fn a ihf iha =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      have hff : fn.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      have hfa : a.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [List.append_assoc, ihf f (encodeOleanExprAux a ++ rest) hff]
      dsimp only
      rw [iha f rest hfa]
  | lam dom body ihd ihb =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      have hfd : dom.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      have hfb : body.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [List.append_assoc, ihd f (encodeOleanExprAux body ++ rest) hfd]
      dsimp only
      rw [ihb f rest hfb]
  | forallE dom body ihd ihb =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      have hfd : dom.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      have hfb : body.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [List.append_assoc, ihd f (encodeOleanExprAux body ++ rest) hfd]
      dsimp only
      rw [ihb f rest hfb]
  | letE ty val body iht ihv ihb =>
    cases fuel with
    | zero => simp [Expr.astSize] at hfuel
    | succ f =>
      have hft : ty.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      have hfv : val.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      have hfb : body.astSize ≤ f := by simp [Expr.astSize] at hfuel; omega
      dsimp [encodeOleanExprAux, decodeOleanExprAux]
      rw [List.append_assoc, List.append_assoc, iht f (encodeOleanExprAux val ++ (encodeOleanExprAux body ++ rest)) hft]
      dsimp only
      rw [ihv f (encodeOleanExprAux body ++ rest) hfv]
      dsimp only
      rw [ihb f rest hfb]

/-- Losslessly encode a `ConLeche.Expr` prefixed by its exact structural fuel `e.astSize`. -/
def encodeOleanExpr (e : Expr) : List UInt8 :=
  encodeNat e.astSize ++ encodeOleanExprAux e

/-- Decode a `ConLeche.Expr` from `stream` without any fixed depth cap. -/
def decodeOleanExprStream (stream : List UInt8) : Option (Expr × List UInt8) :=
  match decodeNat stream with
  | some (fuel, rest1) => decodeOleanExprAux fuel rest1
  | none => none

/-- Unconditional round-trip theorem for `encodeOleanExpr`/`decodeOleanExprStream`. -/
theorem decodeOleanExprStream_encodeOleanExpr (e : Expr) (rest : List UInt8) :
    decodeOleanExprStream (encodeOleanExpr e ++ rest) = some (e, rest) := by
  unfold encodeOleanExpr decodeOleanExprStream
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  exact decodeOleanExprAux_encode e e.astSize rest (Nat.le_refl _)

/-- Losslessly encode a `Decl` (including `name`, `levelParams`, `wfTag`, `ty`, and `val`). -/
def encodeOleanDecl (d : Decl) : List UInt8 :=
  encodeStringStream d.name ++
  encodeStringList d.levelParams ++
  [if d.wfTag then 1 else 0] ++
  encodeOleanExpr d.ty ++
  encodeOleanExpr d.val

/-- Decode a single `Decl` record from `stream`. -/
def decodeOleanDeclStream (stream : List UInt8) : Option (Decl × List UInt8) :=
  match decodeStringStream stream with
  | none => none
  | some (declName, rest1) =>
    match decodeStringList rest1 with
    | none => none
    | some (lparams, rest2) =>
      match rest2 with
      | [] => none
      | wfByte :: rest3 =>
        let wf := wfByte != 0
        match decodeOleanExprStream rest3 with
        | none => none
        | some (ty, rest4) =>
          match decodeOleanExprStream rest4 with
          | none => none
          | some (val, rest5) =>
            some ({ name := declName, levelParams := lparams, ty := ty, val := val, wfTag := wf }, rest5)

/-- Round-trip theorem for `encodeOleanDecl`/`decodeOleanDeclStream`. -/
theorem decodeOleanDeclStream_encodeOleanDecl (d : Decl) (rest : List UInt8) :
    decodeOleanDeclStream (encodeOleanDecl d ++ rest) = some (d, rest) := by
  rcases d with ⟨name, lparams, ty, val, wf⟩
  unfold encodeOleanDecl decodeOleanDeclStream
  simp only [List.append_assoc, decodeStringStream_encodeStringStream, decodeStringList_encodeStringList]
  cases wf <;> simp [decodeOleanExprStream_encodeOleanExpr]

/-- Encode a list of `Decl` records. -/
def encodeOleanDeclsAux : List Decl → List UInt8
  | [] => []
  | d :: rest => encodeOleanDecl d ++ encodeOleanDeclsAux rest

/-- Decode `count` `Decl` records from `stream`. -/
def decodeOleanDeclsStream : Nat → List UInt8 → Option (List Decl × List UInt8)
  | 0, rest => some ([], rest)
  | count + 1, stream =>
    match decodeOleanDeclStream stream with
    | some (d, rest1) =>
      match decodeOleanDeclsStream count rest1 with
      | some (ds, rest2) => some (d :: ds, rest2)
      | none => none
    | none => none

theorem decodeOleanDeclsStream_encode (ds : List Decl) (rest : List UInt8) :
    decodeOleanDeclsStream ds.length (encodeOleanDeclsAux ds ++ rest) = some (ds, rest) := by
  induction ds generalizing rest with
  | nil => rfl
  | cons d ds' ih =>
    dsimp [List.length, encodeOleanDeclsAux, decodeOleanDeclsStream]
    rw [List.append_assoc, decodeOleanDeclStream_encodeOleanDecl]
    dsimp only
    rw [ih rest]

/-- Losslessly encode a `RecRule` (including `recName`, `ctorName`, `levelParams`,
    `isDependent`, `rhsTemplate`, `argDom`, `indTy`, and `resultCod`). -/
def encodeOleanRecRule (r : RecRule) : List UInt8 :=
  encodeStringStream r.recName ++
  encodeStringStream r.ctorName ++
  encodeStringList r.levelParams ++
  [if r.isDependent then 1 else 0] ++
  encodeOleanExpr r.rhsTemplate ++
  encodeOleanExpr r.argDom ++
  encodeOleanExpr r.indTy ++
  encodeOleanExpr r.resultCod

/-- Decode a single `RecRule` record from `stream`. -/
def decodeOleanRecRuleStream (stream : List UInt8) : Option (RecRule × List UInt8) :=
  match decodeStringStream stream with
  | none => none
  | some (rName, rest1) =>
    match decodeStringStream rest1 with
    | none => none
    | some (cName, rest2) =>
      match decodeStringList rest2 with
      | none => none
      | some (lparams, depByte :: rest3) =>
        if depByte != 0 && depByte != 1 then
          none
        else
          match decodeOleanExprStream rest3 with
          | none => none
          | some (rhs, rest4) =>
            match decodeOleanExprStream rest4 with
            | none => none
            | some (argDom, rest5) =>
              match decodeOleanExprStream rest5 with
              | none => none
              | some (indTy, rest6) =>
                match decodeOleanExprStream rest6 with
                | none => none
                | some (resCod, rest7) =>
                  let rule : RecRule := {
                    recName := rName, ctorName := cName, levelParams := lparams,
                    rhsTemplate := rhs, argDom := argDom, indTy := indTy, resultCod := resCod,
                    isDependent := depByte == 1
                  }
                  some (rule, rest7)
      | some (_, []) => none

/-- Round-trip theorem for `encodeOleanRecRule`/`decodeOleanRecRuleStream`. -/
theorem decodeOleanRecRuleStream_encodeOleanRecRule (r : RecRule) (rest : List UInt8) :
    decodeOleanRecRuleStream (encodeOleanRecRule r ++ rest) = some (r, rest) := by
  rcases r with ⟨rName, cName, lparams, rhs, argDom, indTy, resCod, isDep⟩
  unfold encodeOleanRecRule decodeOleanRecRuleStream
  simp only [List.append_assoc, decodeStringStream_encodeStringStream,
    decodeStringList_encodeStringList, List.cons_append, List.nil_append]
  cases isDep <;> simp [decodeOleanExprStream_encodeOleanExpr]

/-- Encode a list of `RecRule` records. -/
def encodeOleanRecRulesAux : List RecRule → List UInt8
  | [] => []
  | r :: rest => encodeOleanRecRule r ++ encodeOleanRecRulesAux rest

/-- Decode `count` `RecRule` records from `stream`. -/
def decodeOleanRecRulesAux : Nat → List UInt8 → Option (List RecRule × List UInt8)
  | 0, rest => some ([], rest)
  | count + 1, stream =>
    match decodeOleanRecRuleStream stream with
    | some (r, rest1) =>
      match decodeOleanRecRulesAux count rest1 with
      | some (rs, rest2) => some (r :: rs, rest2)
      | none => none
    | none => none

theorem decodeOleanRecRulesAux_encode (rs : List RecRule) (rest : List UInt8) :
    decodeOleanRecRulesAux rs.length (encodeOleanRecRulesAux rs ++ rest) = some (rs, rest) := by
  induction rs generalizing rest with
  | nil => rfl
  | cons r rs' ih =>
    dsimp [List.length, encodeOleanRecRulesAux, decodeOleanRecRulesAux]
    rw [List.append_assoc, decodeOleanRecRuleStream_encodeOleanRecRule]
    dsimp only
    rw [ih rest]

/-- Encode `List RecRule` with an unbounded `encodeNat` count prefix. -/
def encodeOleanRecRules (rs : List RecRule) : List UInt8 :=
  encodeNat rs.length ++ encodeOleanRecRulesAux rs

/-- Decode `List RecRule` from `stream`. -/
def decodeOleanRecRulesStream (stream : List UInt8) : Option (List RecRule × List UInt8) :=
  match decodeNat stream with
  | some (n, rest1) => decodeOleanRecRulesAux n rest1
  | none => none

theorem decodeOleanRecRulesStream_encodeOleanRecRules (rs : List RecRule) (rest : List UInt8) :
    decodeOleanRecRulesStream (encodeOleanRecRules rs ++ rest) = some (rs, rest) := by
  unfold encodeOleanRecRules decodeOleanRecRulesStream
  rw [List.append_assoc, decodeNat_encodeNat]
  dsimp only
  exact decodeOleanRecRulesAux_encode rs rest

/-- Incrementally verify that each declaration `d` in a list is well-typed against the
    strictly preceding prefix environment `acc` and has a fresh declaration name. -/
def verifyDeclsPrefix (acc : List Decl) : List Decl → Bool
  | [] => true
  | d :: rest =>
    !(acc.any (fun prev => prev.name == d.name)) &&
    verifyDecl { decls := acc, recRules := [], headerMagic := 0x4F4C454E } d &&
    verifyDeclsPrefix (acc ++ [d]) rest

/-- Global environment well-formedness predicate (`EnvWF`):
    1. All declarations satisfy acyclic incremental prefix typing (`verifyDeclsPrefix [] env.decls = true`).
    2. Every declaration `d ∈ env.decls` is semantically valid (`CICValid env d`).
    3. Every recursor rule `r ∈ env.recRules` is well-typed (`RecRuleWF env r`). -/
def EnvWF (env : Env) : Prop :=
  verifyDeclsPrefix [] env.decls = true ∧
  (∀ d ∈ env.decls, CICValid env d) ∧
  (∀ r ∈ env.recRules, RecRuleWF env r)

/-- Losslessly encode an `Env` into a binary `.olean` shard `ByteArray`
    (`"OLEN"` magic + `encodeNat decls.length` + decl records + `encodeOleanRecRules recRules`). -/
def encodeOleanShard (env : Env) : ByteArray :=
  let header : List UInt8 := [0x4F, 0x4C, 0x45, 0x4E]
  let declPayload := encodeNat env.decls.length ++ encodeOleanDeclsAux env.decls
  let rulePayload := encodeOleanRecRules env.recRules
  ByteArray.mk (header ++ declPayload ++ rulePayload).toArray

/-- Parse and type-check a binary `.olean` shard (`bytes : ByteArray`):
    1. Verifies minimum header size (`bytes.size ≥ 5`), `"OLEN"` magic, and `declCount > 0`.
    2. Decodes `declCount` declarations and `recRules`, and verifies exact byte consumption (`rest == []`).
    3. Verifies acyclic incremental prefix typing (`verifyDeclsPrefix [] decls`), full-environment
       declaration typing (`decls.all (verifyDecl env)`), and recursor rule typing (`recRules.all (verifyRecRule env)`). -/
def parseOleanShard (bytes : ByteArray) : Except String Env :=
  if bytes.size < 5 then
    .error "parseOleanShard: truncated .olean shard (< 5 bytes)"
  else
    match bytes.data.toList with
    | m0 :: m1 :: m2 :: m3 :: payload =>
      if !(m0 == 0x4F && m1 == 0x4C && m2 == 0x45 && m3 == 0x4E) then
        .error "parseOleanShard: invalid .olean header magic (expected OLEN = 0x4F4C454E)"
      else
        match decodeNat payload with
        | none => .error "parseOleanShard: malformed declaration count"
        | some (declCount, rest1) =>
          if declCount == 0 then
            .error "parseOleanShard: empty .olean shard (declCount = 0)"
          else
            match decodeOleanDeclsStream declCount rest1 with
            | none => .error "parseOleanShard: malformed binary declaration stream"
            | some (decls, rest2) =>
              match decodeOleanRecRulesStream rest2 with
              | none => .error "parseOleanShard: malformed binary recursor rule stream"
              | some (recRules, rest3) =>
                let env : Env := { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E }
                if !(rest3 == [] && verifyDeclsPrefix [] decls) then
                  .error "parseOleanShard: trailing bytes or cyclic/duplicate declaration prefix"
                else if decls.all (verifyDecl env) && recRules.all (verifyRecRule env) then
                  .ok env
                else
                  .error "parseOleanShard: CIC kernel rejected declaration or recursor rule in .olean shard"
    | _ => .error "parseOleanShard: truncated .olean header"

/-- Bidirectional type-inference soundness (`inferType_sound`):
    whenever `inferType fuel env ctx e = some ty`, the inductive dependent CIC typing
    derivation `HasType env ctx e ty` holds. -/
theorem inferType_sound (fuel : Nat) (env : Env) (ctx : List Expr) (e ty : Expr)
    (h_infer : inferType fuel env ctx e = some ty) :
    HasType env ctx e ty := by
  induction fuel generalizing ctx e ty with
  | zero =>
    simp [inferType] at h_infer
  | succ fuel' ih =>
    cases e with
    | bvar idx =>
      dsimp [inferType] at h_infer
      cases hctx : ctx[idx]? with
      | none => simp [hctx] at h_infer
      | some bty =>
        simp [hctx] at h_infer
        subst h_infer
        exact HasType.bvar hctx
    | sort u =>
      dsimp [inferType] at h_infer
      injection h_infer with heq
      subst heq
      exact HasType.sort u
    | const name lvls =>
      dsimp [inferType] at h_infer
      cases hlook : env.lookup? name with
      | none => simp [hlook] at h_infer
      | some d =>
        simp only [hlook] at h_infer
        split at h_infer
        · rename_i hcond
          injection h_infer with heq
          subst heq
          simp only [Bool.and_eq_true] at hcond
          exact HasType.const hlook hcond.1 hcond.2
        · contradiction
    | app fn arg =>
      dsimp [inferType] at h_infer
      cases hfn : inferType fuel' env ctx fn with
      | none => simp [hfn] at h_infer
      | some fnTy =>
        cases fnTy with
        | forallE dom body =>
          cases harg : inferType fuel' env ctx arg with
          | none => simp [hfn, harg] at h_infer
          | some argTy =>
            simp only [hfn, harg] at h_infer
            split at h_infer
            · rename_i heqDom
              injection h_infer with hty
              subst hty
              have hdomEq : argTy = dom := of_decide_eq_true heqDom
              subst hdomEq
              exact HasType.app (ih ctx fn (.forallE argTy body) hfn) (ih ctx arg argTy harg)
            · contradiction
        | _ => simp [hfn] at h_infer
    | lam dom body =>
      dsimp [inferType] at h_infer
      cases hdom : inferType fuel' env ctx dom with
      | none => simp [hdom] at h_infer
      | some domTy =>
        cases domTy with
        | sort u =>
          cases hbody : inferType fuel' env (dom :: ctx) body with
          | none => simp [hdom, hbody] at h_infer
          | some bodyTy =>
            simp [hdom, hbody] at h_infer
            subst h_infer
            exact HasType.lam (ih ctx dom (.sort u) hdom) (ih (dom :: ctx) body bodyTy hbody)
        | _ => simp [hdom] at h_infer
    | forallE dom body =>
      dsimp [inferType] at h_infer
      cases hdom : inferType fuel' env ctx dom with
      | none => simp [hdom] at h_infer
      | some domTy =>
        cases domTy with
        | sort u =>
          cases hbody : inferType fuel' env (dom :: ctx) body with
          | none => simp [hdom, hbody] at h_infer
          | some bodyTy =>
            cases bodyTy with
            | sort v =>
              simp [hdom, hbody] at h_infer
              subst h_infer
              exact HasType.forallE (ih ctx dom (.sort u) hdom) (ih (dom :: ctx) body (.sort v) hbody)
            | _ => simp [hdom, hbody] at h_infer
        | _ => simp [hdom] at h_infer
    | letE lTy val body =>
      dsimp [inferType] at h_infer
      cases hty : inferType fuel' env ctx lTy with
      | none => simp [hty] at h_infer
      | some lTySort =>
        cases lTySort with
        | sort u =>
          cases hval : inferType fuel' env ctx val with
          | none => simp [hty, hval] at h_infer
          | some valTy =>
            cases hbody : inferType fuel' env (lTy :: ctx) body with
            | none => simp [hty, hval, hbody] at h_infer
            | some bodyTy =>
              simp only [hty, hval, hbody] at h_infer
              split at h_infer
              · rename_i heqVal
                injection h_infer with hres
                subst hres
                have hvalEq : valTy = lTy := of_decide_eq_true heqVal
                subst hvalEq
                exact HasType.letE
                  (ih ctx valTy (.sort u) hty)
                  (ih ctx val valTy hval)
                  (ih (valTy :: ctx) body bodyTy hbody)
              · contradiction
        | _ => simp [hty] at h_infer

/-- Milestone M2 (Item 2): Machine-checked soundness of `ConLeche.verifyDecl`
    (`con_leche_verify_decl_sound`, `0 sorryAx`). -/
theorem con_leche_verify_decl_sound (env : Env) (d : Decl)
    (h_ver : verifyDecl env d = true) :
    CICValid env d := by
  unfold verifyDecl at h_ver
  cases hwf : d.wfTag with
  | false => simp [hwf] at h_ver
  | true =>
    simp only [hwf, Bool.true_and] at h_ver
    cases hty : inferType 64 env [] d.ty with
    | none => simp [hty] at h_ver
    | some tySort =>
      cases tySort with
      | sort u =>
        cases hval : inferType 64 env [] d.val with
        | none => simp [hty, hval] at h_ver
        | some valTy =>
          simp only [hty, hval] at h_ver
          have hHasTy : HasType env [] d.ty (.sort u) :=
            inferType_sound 64 env [] d.ty (.sort u) hty
          have hHasVal : HasType env [] d.val valTy :=
            inferType_sound 64 env [] d.val valTy hval
          refine ⟨hwf, ⟨u, hHasTy⟩, ?_⟩
          exact HasType.conv hHasVal hHasTy h_ver
      | _ => simp [hty] at h_ver

/-- Machine-checked soundness of `verifyRecRuleInst`: any rule instantiation accepted by
    `verifyRecRuleInst env ctx rule lvls` satisfies `RecRuleInstWF env ctx rule lvls`. -/
theorem verifyRecRuleInst_sound (env : Env) (ctx : List Expr) (rule : RecRule) (lvls : List Level)
    (h_ver : verifyRecRuleInst env ctx rule lvls = true) :
    RecRuleInstWF env ctx rule lvls := by
  unfold verifyRecRuleInst at h_ver
  dsimp only at h_ver
  cases har : (rule.levelParams.length == lvls.length) with
  | false => simp [har] at h_ver
  | true =>
    simp only [har, Bool.true_and] at h_ver
    cases h1 : inferType 64 env ctx (.const rule.ctorName lvls) with
    | none => simp [h1] at h_ver
    | some ctorTy =>
      cases h2 : inferType 64 env ctx (.const rule.recName lvls) with
      | none => simp [h1, h2] at h_ver
      | some recTy =>
        cases h3 : inferType 64 env ctx
            (Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate) with
        | none => simp [h1, h2, h3] at h_ver
        | some rhsTy =>
          simp only [h1, h2, h3, Bool.and_eq_true, decide_eq_true_eq] at h_ver
          rcases h_ver with ⟨⟨heq1, heq2⟩, heq3⟩
          subst heq1
          subst heq2
          subst heq3
          refine ⟨har, ?_, ?_, ?_⟩
          · exact inferType_sound 64 env ctx _ _ h1
          · exact inferType_sound 64 env ctx _ _ h2
          · exact inferType_sound 64 env ctx _ _ h3

/-- Machine-checked soundness of `verifyRecRule`: any rule accepted by `verifyRecRule` satisfies `RecRuleWF`. -/
theorem verifyRecRule_sound (env : Env) (rule : RecRule)
    (h_ver : verifyRecRule env rule = true) :
    RecRuleWF env rule :=
  verifyRecRuleInst_sound env [] rule (rule.levelParams.map Level.param) h_ver

/-- Environment well-formedness theorem for parsed `.olean` shards (`parseOleanShard_envWF`, `0 sorryAx`):
    any shard accepted by `parseOleanShard` satisfies `EnvWF env` (acyclic incremental prefix typing,
    semantic `CICValid` for all declarations, and well-formed `recRules`). -/
theorem parseOleanShard_envWF (bytes : ByteArray) (env : Env)
    (h_parse : parseOleanShard bytes = .ok env) :
    EnvWF env := by
  unfold parseOleanShard at h_parse
  split at h_parse
  · contradiction
  · split at h_parse
    · rename_i m0 m1 m2 m3 payload _
      split at h_parse
      · contradiction
      · cases hcnt : decodeNat payload with
        | none => simp [hcnt] at h_parse
        | some cntPair =>
          rcases cntPair with ⟨declCount, rest1⟩
          simp only [hcnt] at h_parse
          split at h_parse
          · contradiction
          · cases hdec : decodeOleanDeclsStream declCount rest1 with
            | none => simp [hdec] at h_parse
            | some declPair =>
              rcases declPair with ⟨decls, rest2⟩
              simp only [hdec] at h_parse
              cases hrul : decodeOleanRecRulesStream rest2 with
              | none => simp [hrul] at h_parse
              | some rulePair =>
                rcases rulePair with ⟨recRules, rest3⟩
                simp only [hrul] at h_parse
                split at h_parse
                · contradiction
                · rename_i hnot
                  split at h_parse
                  · rename_i hall
                    injection h_parse with henv
                    subst henv
                    simp only [Bool.and_eq_true] at hall
                    have hpref : verifyDeclsPrefix [] decls = true := by
                      revert hnot
                      cases verifyDeclsPrefix [] decls <;> simp
                    refine ⟨hpref, ?_, ?_⟩
                    · intro d hd
                      have hver :
                          verifyDecl { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E } d =
                            true :=
                        List.all_eq_true.mp hall.1 d hd
                      exact
                        con_leche_verify_decl_sound
                          { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E } d hver
                    · intro r hr
                      have hrv :
                          verifyRecRule { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E } r =
                            true :=
                        List.all_eq_true.mp hall.2 r hr
                      exact
                        verifyRecRule_sound
                          { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E } r hrv
                  · contradiction
    · contradiction

/-- Milestone M2 (Item 1): Machine-checked soundness of the `.olean` binary shard parser
    (`olean_mmap_bridge_sound`, `0 sorryAx`). -/
theorem olean_mmap_bridge_sound (bytes : ByteArray) (env : Env)
    (h_parse : parseOleanShard bytes = .ok env) :
    bytes.size ≥ 5 ∧
    env.headerMagic = 0x4F4C454E ∧
    verifyDeclsPrefix [] env.decls = true ∧
    (∀ d ∈ env.decls, CICValid env d) ∧
    (∀ r ∈ env.recRules, RecRuleWF env r) := by
  have ⟨hpref, hd, hr⟩ := parseOleanShard_envWF bytes env h_parse
  unfold parseOleanShard at h_parse
  split at h_parse
  · contradiction
  · rename_i hlt
    have hsize : bytes.size ≥ 5 := Nat.le_of_not_lt hlt
    split at h_parse
    · rename_i m0 m1 m2 m3 payload _
      split at h_parse
      · contradiction
      · cases hcnt : decodeNat payload with
        | none => simp [hcnt] at h_parse
        | some cntPair =>
          rcases cntPair with ⟨declCount, rest1⟩
          simp only [hcnt] at h_parse
          split at h_parse
          · contradiction
          · cases hdec : decodeOleanDeclsStream declCount rest1 with
            | none => simp [hdec] at h_parse
            | some declPair =>
              rcases declPair with ⟨decls, rest2⟩
              simp only [hdec] at h_parse
              cases hrul : decodeOleanRecRulesStream rest2 with
              | none => simp [hrul] at h_parse
              | some rulePair =>
                rcases rulePair with ⟨recRules, rest3⟩
                simp only [hrul] at h_parse
                split at h_parse
                · contradiction
                · split at h_parse
                  · injection h_parse with henv
                    subst henv
                    exact ⟨hsize, rfl, hpref, hd, hr⟩
                  · contradiction
    · contradiction

/-- Full end-to-end binary `.olean` shard round-trip theorem (`parseOleanShard_encodeOleanShard_roundtrip`, `0 sorryAx`):
    any verified non-empty environment `env` with `"OLEN"` magic serializes via `encodeOleanShard`
    and parses back via `parseOleanShard` to `.ok env`. -/
theorem parseOleanShard_encodeOleanShard_roundtrip (env : Env)
    (h_magic : env.headerMagic = 0x4F4C454E)
    (h_nonempty : env.decls ≠ [])
    (h_pref : verifyDeclsPrefix [] env.decls = true)
    (h_decls : env.decls.all (verifyDecl env) = true)
    (h_rules : env.recRules.all (verifyRecRule env) = true) :
    parseOleanShard (encodeOleanShard env) = .ok env := by
  rcases env with ⟨decls, recRules, magic⟩
  dsimp only at h_magic h_nonempty h_pref h_decls h_rules
  subst h_magic
  have hlen_pos : decls.length > 0 := by
    cases decls with
    | nil => contradiction
    | cons _ _ => simp
  have h_size_not_lt : ¬((encodeOleanShard { decls := decls, recRules := recRules, headerMagic := 0x4F4C454E }).size < 5) := by
    unfold encodeOleanShard
    cases hlen : decls.length with
    | zero => omega
    | succ k =>
      simp [encodeNat, ByteArray.size]
  unfold parseOleanShard
  simp only [h_size_not_lt, ↓reduceIte]
  unfold encodeOleanShard
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  have h_dec_nat : decodeNat (encodeNat decls.length ++ (encodeOleanDeclsAux decls ++ encodeOleanRecRules recRules)) =
      some (decls.length, encodeOleanDeclsAux decls ++ encodeOleanRecRules recRules) :=
    decodeNat_encodeNat decls.length (encodeOleanDeclsAux decls ++ encodeOleanRecRules recRules)
  have h_cnt_ne : (decls.length == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have h_rules_dec : decodeOleanRecRulesStream (encodeOleanRecRules recRules) = some (recRules, []) := by
    simpa using decodeOleanRecRulesStream_encodeOleanRecRules recRules []
  simp [h_dec_nat, h_cnt_ne, decodeOleanDeclsStream_encode, h_rules_dec, h_pref, h_decls, h_rules]

/-- Single-step WHNF $\iota$-reduction lemma (`whnf_one_iota`):
    whenever `applyIotaRules env.recRules (.app fn arg) = some red`, `whnf 1 env (.app fn arg)`
    evaluates directly to `red`. -/
theorem whnf_one_iota (env : Env) (fn arg red : Expr)
    (h_active : applyIotaRules env.recRules (.app fn arg) = some red) :
    whnf 1 env (.app fn arg) = red := by
  unfold whnf
  dsimp only
  rw [h_active]
  rfl

/-- Subject reduction & definitional equality for universe-polymorphic inductive recursor $\iota$-reduction
    in an arbitrary typing context `ctx` for both non-dependent (`rule.isDependent = false`) and
    dependent-motive (`rule.isDependent = true`) rules (`evalIotaStep_sound`, `0 sorryAx`):
    whenever `RecRuleInstWF env ctx rule lvls` holds (e.g. via `verifyRecRuleInst_sound`), `rule` is active in
    `env.recRules`, and `payload` has type `argDomInst`:
    1. The unreduced elimination redex `e = .app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)`
       has type `rule.iotaResultTy lvls payload` in `ctx`.
    2. The $\iota$-reduced contractum `red = .app rhsInst payload` has the exact same type
       `rule.iotaResultTy lvls payload` in `ctx` (Subject Reduction).
    3. The kernel's `whnf` / `isDefEq` engine reduces `e` to `red` (`isDefEq 2 env e red = true`). -/
theorem evalIotaStep_sound (env : Env) (ctx : List Expr) (rule : RecRule) (lvls : List Level)
    (payload red : Expr)
    (h_step : evalIotaStep rule (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)) = some red)
    (h_active : applyIotaRules env.recRules (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)) = some red)
    (h_wf : RecRuleInstWF env ctx rule lvls)
    (h_arg : HasType env ctx payload (Expr.instantiateLevelParams rule.levelParams lvls rule.argDom)) :
    let redex := Expr.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)
    let rhsInst := Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate
    red = .app rhsInst payload ∧
    HasType env ctx redex (rule.iotaResultTy lvls payload) ∧
    HasType env ctx red (rule.iotaResultTy lvls payload) ∧
    isDefEq 2 env redex red = true := by
  rcases h_wf with ⟨h_arity, h_ctor, h_rec, h_rhs⟩
  dsimp [evalIotaStep] at h_step
  simp only [beq_self_eq_true, decide_true, h_arity, Bool.and_self, ↓reduceIte, Option.some.injEq] at h_step
  subst h_step
  let indTyInst := Expr.instantiateLevelParams rule.levelParams lvls rule.indTy
  let resCodInst := Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod
  have h_ctor_app : HasType env ctx (.app (.const rule.ctorName lvls) payload) indTyInst := by
    unfold RecRule.ctorExpectedInst at h_ctor
    have h1 := HasType.app h_ctor h_arg
    rwa [Expr.inst0_lift1 payload indTyInst] at h1
  have h_redex_ty : HasType env ctx (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload))
      (rule.iotaResultTy lvls payload) := by
    unfold RecRule.recExpectedInst at h_rec
    unfold RecRule.iotaResultTy
    cases hdep : rule.isDependent with
    | false =>
      simp only [hdep, Bool.false_eq_true, ↓reduceIte] at h_rec ⊢
      have h2 := HasType.app h_rec h_ctor_app
      rwa [Expr.inst0_lift1 (.app (.const rule.ctorName lvls) payload) resCodInst] at h2
    | true =>
      simp only [hdep, ↓reduceIte] at h_rec ⊢
      have h2 := HasType.app h_rec h_ctor_app
      have h_inst_dep : Expr.inst0 (.app (.const rule.ctorName lvls) payload) (.app (Expr.lift 1 0 resCodInst) (.bvar 0)) =
          .app resCodInst (.app (.const rule.ctorName lvls) payload) := by
        change Expr.app (Expr.inst0 (.app (.const rule.ctorName lvls) payload) (Expr.lift 1 0 resCodInst))
            (Expr.inst0 (.app (.const rule.ctorName lvls) payload) (.bvar 0)) =
          .app resCodInst (.app (.const rule.ctorName lvls) payload)
        rw [Expr.inst0_lift1, Expr.inst0_bvar0]
      rwa [h_inst_dep] at h2
  have h_red_ty : HasType env ctx (.app (Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate) payload)
      (rule.iotaResultTy lvls payload) := by
    unfold RecRule.rhsExpectedInst at h_rhs
    unfold RecRule.iotaResultTy
    cases hdep : rule.isDependent with
    | false =>
      simp only [hdep, Bool.false_eq_true, ↓reduceIte] at h_rhs ⊢
      have h3 := HasType.app h_rhs h_arg
      rwa [Expr.inst0_lift1 payload resCodInst] at h3
    | true =>
      simp only [hdep, ↓reduceIte] at h_rhs ⊢
      have h3 := HasType.app h_rhs h_arg
      have h_inst_rhs : Expr.inst0 payload (.app (Expr.lift 1 0 resCodInst) (.app (.const rule.ctorName lvls) (.bvar 0))) =
          .app resCodInst (.app (.const rule.ctorName lvls) payload) := by
        change Expr.app (Expr.inst0 payload (Expr.lift 1 0 resCodInst))
            (Expr.app (.const rule.ctorName lvls) (Expr.inst0 payload (.bvar 0))) =
          .app resCodInst (.app (.const rule.ctorName lvls) payload)
        rw [Expr.inst0_lift1, Expr.inst0_bvar0]
      rwa [h_inst_rhs] at h3
  have hw : whnf 1 env (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)) =
      .app (Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate) payload :=
    whnf_one_iota env (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)
      (.app (Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate) payload) h_active
  have h_defeq : isDefEq 2 env (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload))
      (.app (Expr.instantiateLevelParams rule.levelParams lvls rule.rhsTemplate) payload) = true := by
    unfold isDefEq
    dsimp only
    rw [hw]
    simp
  exact ⟨rfl, h_redex_ty, h_red_ty, h_defeq⟩

/-- Dependent-motive Subject Reduction for inductive recursor $\iota$-reduction derived directly from
    computable rule verification `verifyRecRuleInst env ctx rule lvls = true`
    (`evalIotaStep_dependent_sound`, `0 sorryAx`):
    whenever `rule.isDependent = true` and `verifyRecRuleInst env ctx rule lvls = true` accepts `rule`,
    both the unreduced redex and the $\iota$-reduced contractum have the dependent motive application type
    `.app (Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod) (.app (.const rule.ctorName lvls) payload)`. -/
theorem evalIotaStep_dependent_sound (env : Env) (ctx : List Expr) (rule : RecRule) (lvls : List Level)
    (payload red : Expr)
    (h_dep : rule.isDependent = true)
    (h_ver : verifyRecRuleInst env ctx rule lvls = true)
    (h_step : evalIotaStep rule (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)) = some red)
    (h_active : applyIotaRules env.recRules (.app (.const rule.recName lvls) (.app (.const rule.ctorName lvls) payload)) = some red)
    (h_arg : HasType env ctx payload (Expr.instantiateLevelParams rule.levelParams lvls rule.argDom)) :
    let ctorApp := Expr.app (.const rule.ctorName lvls) payload
    let redex := Expr.app (.const rule.recName lvls) ctorApp
    let motiveInst := Expr.instantiateLevelParams rule.levelParams lvls rule.resultCod
    let depTy := Expr.app motiveInst ctorApp
    HasType env ctx redex depTy ∧
    HasType env ctx red depTy ∧
    isDefEq 2 env redex red = true := by
  have h_wf : RecRuleInstWF env ctx rule lvls :=
    verifyRecRuleInst_sound env ctx rule lvls h_ver
  have h_main := evalIotaStep_sound env ctx rule lvls payload red h_step h_active h_wf h_arg
  rcases h_main with ⟨_, h_redex, h_red, h_defeq⟩
  unfold RecRule.iotaResultTy at h_redex h_red
  simp only [h_dep, ↓reduceIte] at h_redex h_red
  exact ⟨h_redex, h_red, h_defeq⟩

end ConLeche
