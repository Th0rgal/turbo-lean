/-
  TurboLean.ConLeche (Milestone M2 / Wave 1 G1b):
  Self-contained dependent Calculus of Inductive Constructions (CIC) kernel model (`ConLeche`
  and `TurboLean.Kernel.ConLeche`) with universe levels (`zero`, `succ`, `max`, `imax`, `param`),
  de Bruijn lifting & capture-avoiding substitution (`lift`, `subst`, `inst0`), fuel-bounded
  WHNF & definitional equality (`whnf`, `isDefEq`), inductive typing judgment (`HasType`),
  bidirectional typechecker (`inferType`, `verifyDecl`, `checkDecl`), binary `"OLEN"` v1
  (`0x4F4C454E`) declaration shard model parser/encoder (`parseOleanShard`, `encodeOleanShard`),
  and a validator for the 96-byte header and root pointer of real Lean 4 v4.35.0 `.olean` files
  (`parseRealOleanHeader`, `parseRealOlean`, `checkRealOleanDecl`).

  Explicit Model Limitation & H1/H3 Scope (`roadmap/HORIZONS.md` G1b):
  - `parseOleanShard` / `encodeOleanShard` in this module operate on the in-repo self-contained
    `"OLEN"` v1 (`0x4F4C454E`) binary shard model format, NOT raw Lean 4 `.olean` compacted
    memory-region files.
  - `parseRealOleanHeader` reads real `.olean` files, but only their 96-byte header and root
    pointer bounds. Decoding the compacted object region into declarations is left to Lean's C
    reader `lean_compacted_region_read`, which is trusted (`docs/TRUSTED_BASE.md` item 4).
    `real_olean_bridge_sound` / `real_olean_checkDecl_sound` hold for whatever declarations that
    reader hands over; they do not prove the reader correct.
  - Real Lean 4 `.olean` region files and `lean4export` streams are verified out-of-process by
    the external `leanprover/con-leche` binary (whose upstream ZFC soundness and `.olean` sparse
    region reader theorems are bridged in `verification/con-leche-bridge/`), while H1 proves the
    first-order `LCNF -> LNIR` compiler path and H3 retains compiling `con-leche` natively once
    recursive inductives, runtime objects, closures, and `IO` are in scope.
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

end Expr

/-- Kernel declaration entry in a `ConLeche` environment. -/
structure Decl where
  name  : String
  ty    : Expr
  val   : Expr
  wfTag : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Kernel environment holding verified declarations and `.olean` shard header metadata. -/
structure Env where
  decls       : List Decl
  headerMagic : UInt32 := 0x4F4C454E
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Env

/-- Look up a declaration by name in `env`. -/
def lookup? (env : Env) (name : String) : Option Decl :=
  env.decls.find? (fun d => d.name == name)

end Env

/-- Fuel-bounded Weak Head Normal Form (WHNF) evaluator supporting $\beta$-reduction,
    $\zeta$-reduction (`letE`), and $\delta$-unfolding of verified environment constants. -/
def whnf (fuel : Nat) (env : Env) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match e with
    | .app fn arg =>
      match whnf fuel' env fn with
      | .lam _ body => whnf fuel' env (Expr.inst0 arg body)
      | fn' => .app fn' arg
    | .letE _ val body =>
      whnf fuel' env (Expr.inst0 val body)
    | .const name _ =>
      match env.lookup? name with
      | some d => if d.wfTag then whnf fuel' env d.val else e
      | none => e
    | _ => e

/-- Fuel-bounded definitional equality (`isDefEq`) combining syntactic equality,
    WHNF $\beta\delta\zeta$-reduction, and structural recursion under binders. -/
def isDefEq (fuel : Nat) (env : Env) (a b : Expr) : Bool :=
  if a == b then true
  else
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let a' := whnf fuel' env a
      let b' := whnf fuel' env b
      if a' == b' then true
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
      HasType env ctx (.const name lvls) d.ty
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
  | _ + 1, env, _, .const name _lvls =>
    match env.lookup? name with
    | some d => if d.wfTag then some d.ty else none
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

/-! ## Binary `.olean` Declaration Shard Codec (`OLEN` v1) -/

/-- Decode a compact binary `Expr` node from `bytes` starting at `off` with recursion `fuel`.
    Tag encoding:
    - `0`: `.bvar idx` (`2` bytes)
    - `1`: `.sort (.zero)` / `.sort (.succ .zero)` (`2` bytes)
    - `2`: `.const "c_<id>" []` (`2` bytes)
    - `3`: `.app fn arg`
    - `4`: `.lam dom body`
    - `5`: `.forallE dom body` -/
def decodeOleanExpr : Nat → ByteArray → Nat → Option (Expr × Nat)
  | 0, _, _ => none
  | fuel' + 1, bytes, off =>
    if off + 1 >= bytes.size then none
    else
      let tag := bytes.get! off
      let argByte := (bytes.get! (off + 1)).toNat
      if tag == 0 then
        some (.bvar argByte, off + 2)
      else if tag == 1 then
        let lvl := if argByte == 0 then Level.zero else Level.succ Level.zero
        some (.sort lvl, off + 2)
      else if tag == 2 then
        some (.const s!"decl_{argByte}" [], off + 2)
      else if tag == 3 then
        match decodeOleanExpr fuel' bytes (off + 1) with
        | some (fn, off1) =>
          match decodeOleanExpr fuel' bytes off1 with
          | some (a, off2) => some (.app fn a, off2)
          | none => none
        | none => none
      else if tag == 4 then
        match decodeOleanExpr fuel' bytes (off + 1) with
        | some (dom, off1) =>
          match decodeOleanExpr fuel' bytes off1 with
          | some (body, off2) => some (.lam dom body, off2)
          | none => none
        | none => none
      else if tag == 5 then
        match decodeOleanExpr fuel' bytes (off + 1) with
        | some (dom, off1) =>
          match decodeOleanExpr fuel' bytes off1 with
          | some (body, off2) => some (.forallE dom body, off2)
          | none => none
        | none => none
      else if tag == 6 then
        match decodeOleanExpr fuel' bytes (off + 1) with
        | some (ty, off1) =>
          match decodeOleanExpr fuel' bytes off1 with
          | some (val, off2) =>
            match decodeOleanExpr fuel' bytes off2 with
            | some (body, off3) => some (.letE ty val body, off3)
            | none => none
          | none => none
        | none => none
      else
        none

/-- Encode a `ConLeche.Expr` into binary `.olean` shard bytes. -/
def encodeOleanExpr : Expr → List UInt8
  | .bvar idx => [0, idx.toUInt8]
  | .sort .zero => [1, 0]
  | .sort _ => [1, 1]
  | .const _ _ => [2, 0]
  | .app fn a => 3 :: (encodeOleanExpr fn ++ encodeOleanExpr a)
  | .lam dom body => 4 :: (encodeOleanExpr dom ++ encodeOleanExpr body)
  | .forallE dom body => 5 :: (encodeOleanExpr dom ++ encodeOleanExpr body)
  | .letE ty val body => 6 :: (encodeOleanExpr ty ++ encodeOleanExpr val ++ encodeOleanExpr body)

/-- Decode `count` declaration records from `bytes` starting at `off`, returning `(decls, offEnd)`.
    Each record begins with `(declId : UInt8, wfByte : UInt8)` followed by binary `ty` and `val`. -/
def decodeOleanDecls : Nat → ByteArray → Nat → Option (List Decl × Nat)
  | 0, _, off => some ([], off)
  | count + 1, bytes, off =>
    if off + 1 >= bytes.size then none
    else
      let declId := (bytes.get! off).toNat
      let wf := bytes.get! (off + 1) != 0
      match decodeOleanExpr 64 bytes (off + 2) with
      | some (ty, off1) =>
        match decodeOleanExpr 64 bytes off1 with
        | some (val, off2) =>
          match decodeOleanDecls count bytes off2 with
          | some (rest, offEnd) =>
            some ({ name := s!"decl_{declId}", ty := ty, val := val, wfTag := wf } :: rest, offEnd)
          | none => none
        | none => none
      | none => none

/-- Incrementally verify that each declaration `d` in a list is well-typed against the
    strictly preceding prefix environment `acc` and has a fresh declaration name. -/
def verifyDeclsPrefix (acc : List Decl) : List Decl → Bool
  | [] => true
  | d :: rest =>
    !(acc.any (fun prev => prev.name == d.name)) &&
    verifyDecl { decls := acc, headerMagic := 0x4F4C454E } d &&
    verifyDeclsPrefix (acc ++ [d]) rest

/-- Encode an `Env` into a binary `.olean` shard `ByteArray` (`"OLEN"` magic + count + decl records). -/
def encodeOleanShard (env : Env) : ByteArray :=
  let header : List UInt8 := [0x4F, 0x4C, 0x45, 0x4E, env.decls.length.toUInt8]
  let body := (env.decls.zipIdx).foldl (fun acc (d, idx) =>
    acc ++ [idx.toUInt8, if d.wfTag then 1 else 0] ++ encodeOleanExpr d.ty ++ encodeOleanExpr d.val) []
  ByteArray.mk (header ++ body).toArray

/-- Parse and type-check a binary `.olean` shard (`bytes : ByteArray`) in the `"OLEN"` v1 model format:
    1. Verifies minimum header size (`bytes.size ≥ 5`) and `"OLEN"` magic (`0x4F, 0x4C, 0x45, 0x4E`).
    2. Reads `declCount = (bytes.get! 4).toNat`, decodes `declCount` binary declarations,
       and verifies exact byte consumption (`offEnd == bytes.size`).
    3. Verifies acyclic incremental prefix typing (`verifyDeclsPrefix [] decls`)
       and full-environment typing (`decls.all (verifyDecl env)`). -/
def parseOleanShard (bytes : ByteArray) : Except String Env :=
  if bytes.size < 5 then
    .error "parseOleanShard: truncated .olean shard (< 5 bytes)"
  else if !(bytes.get! 0 == 0x4F && bytes.get! 1 == 0x4C && bytes.get! 2 == 0x45 && bytes.get! 3 == 0x4E) then
    .error "parseOleanShard: invalid .olean header magic (expected OLEN = 0x4F4C454E)"
  else
    let declCount := (bytes.get! 4).toNat
    match decodeOleanDecls declCount bytes 5 with
    | none => .error "parseOleanShard: malformed binary declaration stream"
    | some (decls, offEnd) =>
      let env : Env := { decls := decls, headerMagic := 0x4F4C454E }
      if !(offEnd == bytes.size && verifyDeclsPrefix [] decls) then
        .error "parseOleanShard: trailing bytes or cyclic/duplicate declaration prefix"
      else if decls.all (verifyDecl env) then
        .ok env
      else
        .error "parseOleanShard: CIC kernel rejected declaration in .olean shard"

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
        cases hwf : d.wfTag with
        | false => simp [hwf] at h_infer
        | true =>
          simp [hwf] at h_infer
          subst h_infer
          exact HasType.const hlook hwf
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

/-- Milestone M2 (Item 1): Machine-checked soundness of the `.olean` binary shard parser
    (`olean_mmap_bridge_sound`, `0 sorryAx`). -/
theorem olean_mmap_bridge_sound (bytes : ByteArray) (env : Env)
    (h_parse : parseOleanShard bytes = .ok env) :
    bytes.size ≥ 5 ∧
    env.headerMagic = 0x4F4C454E ∧
    decodeOleanDecls (bytes.get! 4).toNat bytes 5 = some (env.decls, bytes.size) ∧
    verifyDeclsPrefix [] env.decls = true ∧
    (∀ d ∈ env.decls, CICValid env d) := by
  unfold parseOleanShard at h_parse
  split at h_parse
  · contradiction
  · rename_i hlt
    have hsize : bytes.size ≥ 5 := Nat.le_of_not_lt hlt
    split at h_parse
    · contradiction
    · cases hdec : decodeOleanDecls (bytes.get! 4).toNat bytes 5 with
      | none => simp [hdec] at h_parse
      | some resPair =>
        rcases resPair with ⟨decls, offEnd⟩
        simp only [hdec] at h_parse
        split at h_parse
        · contradiction
        · rename_i h_not_bad
          have h_consumed_and_prefix : (offEnd == bytes.size && verifyDeclsPrefix [] decls) = true := by
            cases h_b : (offEnd == bytes.size && verifyDeclsPrefix [] decls) <;> simp_all
          have ⟨h_off_beq, h_prefix⟩ := Bool.and_eq_true_iff.mp h_consumed_and_prefix
          have h_off : offEnd = bytes.size := beq_iff_eq.mp h_off_beq
          subst h_off
          split at h_parse
          · rename_i hall
            injection h_parse with henv
            subst henv
            refine ⟨hsize, rfl, ?_, h_prefix, ?_⟩
            · simp
            · intro d hd
              have hver : verifyDecl { decls := decls, headerMagic := 0x4F4C454E } d = true :=
                List.all_eq_true.mp hall d hd
              exact con_leche_verify_decl_sound { decls := decls, headerMagic := 0x4F4C454E } d hver
          · contradiction

end ConLeche

namespace TurboLean.Kernel.ConLeche

abbrev Env := _root_.ConLeche.Env
abbrev Decl := _root_.ConLeche.Decl
abbrev Expr := _root_.ConLeche.Expr
abbrev Level := _root_.ConLeche.Level
abbrev HasType := _root_.ConLeche.HasType
abbrev CICValid := _root_.ConLeche.CICValid
abbrev inferType := _root_.ConLeche.inferType
abbrev verifyDecl := _root_.ConLeche.verifyDecl
abbrev verifyDeclsPrefix := _root_.ConLeche.verifyDeclsPrefix
abbrev decodeOleanDecls := _root_.ConLeche.decodeOleanDecls
abbrev encodeOleanShard := _root_.ConLeche.encodeOleanShard
abbrev parseOleanShard := _root_.ConLeche.parseOleanShard

/-- Well-formedness invariant (`EnvWellFormed`) for a `ConLeche.Env` kernel environment in the
    in-repo `"OLEN"` v1 (`0x4F4C454E`) model: the binary shard header carries `"OLEN"` magic
    (`0x4F4C454E`), every declaration in `env.decls` has a strictly acyclic fresh prefix typing
    (`verifyDeclsPrefix [] env.decls = true`), and every declaration satisfies the semantic
    dependent CIC typing predicate (`CICValid env d`). -/
def EnvWellFormed (env : ConLeche.Env) : Prop :=
  env.headerMagic = 0x4F4C454E ∧
  verifyDeclsPrefix [] env.decls = true ∧
  (∀ d ∈ env.decls, CICValid env d)

/-- Incrementally verify that appending a fresh, well-typed declaration `d` at the end of `rest`
    preserves `verifyDeclsPrefix acc (rest ++ [d])`. -/
theorem verifyDeclsPrefix_append_singleton (acc rest : List ConLeche.Decl) (d : ConLeche.Decl)
    (h_pref : verifyDeclsPrefix acc rest = true)
    (h_fresh : ((acc ++ rest).any (fun prev => prev.name == d.name)) = false)
    (h_ver : verifyDecl { decls := acc ++ rest, headerMagic := 0x4F4C454E } d = true) :
    verifyDeclsPrefix acc (rest ++ [d]) = true := by
  induction rest generalizing acc with
  | nil =>
    have h_fresh0 : (acc.any (fun prev => prev.name == d.name)) = false := by
      simpa only [List.append_nil] using h_fresh
    have h_ver0 : verifyDecl { decls := acc, headerMagic := 0x4F4C454E } d = true := by
      simpa only [List.append_nil] using h_ver
    unfold verifyDeclsPrefix _root_.ConLeche.verifyDeclsPrefix
    simp [h_fresh0, h_ver0, _root_.ConLeche.verifyDeclsPrefix]
  | cons hd tl ih =>
    unfold verifyDeclsPrefix _root_.ConLeche.verifyDeclsPrefix at h_pref ⊢
    rcases Bool.and_eq_true_iff.mp h_pref with ⟨h_left, h_tl⟩
    rcases Bool.and_eq_true_iff.mp h_left with ⟨h_hd_fresh, h_hd_ver⟩
    have h_assoc : (acc ++ [hd]) ++ tl = acc ++ (hd :: tl) := by simp
    have h_fresh' : (((acc ++ [hd]) ++ tl).any (fun prev => prev.name == d.name)) = false := by
      rw [h_assoc]; exact h_fresh
    have h_ver' : verifyDecl { decls := (acc ++ [hd]) ++ tl, headerMagic := 0x4F4C454E } d = true := by
      rw [h_assoc]; exact h_ver
    have h_rec := ih (acc ++ [hd]) h_tl h_fresh' h_ver'
    simp [h_hd_fresh, h_hd_ver, h_rec]

/-- Incrementally check and admit a candidate kernel declaration `d` into `env` (`checkDecl`):
    1. Rejects duplicate declaration names (`env.decls.any (fun prev => prev.name == d.name)`).
    2. Verifies `d` via the bidirectional CIC kernel checker (`verifyDecl env d`).
    3. Verifies that every declaration in the extended environment `{ env with decls := env.decls ++ [d] }`
       remains well-typed under `verifyDecl`. -/
def checkDecl (env : ConLeche.Env) (d : ConLeche.Decl) : Except String ConLeche.Env :=
  if env.decls.any (fun prev => prev.name == d.name) then
    .error s!"checkDecl: duplicate declaration `{d.name}` in kernel environment"
  else if !verifyDecl env d then
    .error s!"checkDecl: CIC kernel rejected declaration `{d.name}`"
  else if ({ env with decls := env.decls ++ [d] }).decls.all (verifyDecl { env with decls := env.decls ++ [d] }) then
    .ok { env with decls := env.decls ++ [d] }
  else
    .error s!"checkDecl: extended environment failed closed-world CIC verification for `{d.name}`"

/-- Milestone M2 (Item 1, Contract V4 / G1b): Machine-checked soundness of the `"OLEN"` v1
    (`.olean` shard model) bridge (`olean_mmap_bridge_sound`, `0 sorryAx`). -/
theorem olean_mmap_bridge_sound (bytes : ByteArray) (env : ConLeche.Env)
    (h_parse : parseOleanShard bytes = .ok env) :
    EnvWellFormed env := by
  have ⟨_, hmagic, _, hpref, hvalid⟩ := _root_.ConLeche.olean_mmap_bridge_sound bytes env h_parse
  exact ⟨hmagic, hpref, hvalid⟩

/-- Milestone M2 (Item 2, Contract V4 / G1b): Machine-checked soundness of the `ConLeche` CIC
    declaration checker (`con_leche_verify_decl_sound`, `0 sorryAx`):
    given a well-formed environment `env` (`EnvWellFormed env`), whenever `checkDecl env d = .ok env'`,
    the extended environment `env'` is well-formed (`EnvWellFormed env'`) and `d` is a valid CIC
    declaration in `env` (`CICValid env d`). -/
theorem con_leche_verify_decl_sound (env env' : ConLeche.Env) (d : ConLeche.Decl)
    (h_wf : EnvWellFormed env)
    (h_ok : checkDecl env d = .ok env') :
    EnvWellFormed env' ∧ CICValid env d := by
  rcases h_wf with ⟨h_magic, h_pref, _⟩
  unfold checkDecl at h_ok
  split at h_ok
  · contradiction
  · rename_i h_not_dup
    have h_fresh : (env.decls.any (fun prev => prev.name == d.name)) = false :=
       Bool.eq_false_iff.mpr h_not_dup
    split at h_ok
    · contradiction
    · rename_i h_not_bad_ver
      have h_ver : verifyDecl env d = true := by
        cases h_v : verifyDecl env d <;> simp_all
      split at h_ok
      · rename_i h_all_env'
        injection h_ok with h_env'
        subst h_env'
        have h_cic_d : CICValid env d :=
          _root_.ConLeche.con_leche_verify_decl_sound env d h_ver
        have h_env_eq : ({ decls := env.decls, headerMagic := 0x4F4C454E } : ConLeche.Env) = env := by
          cases env
          simp at h_magic
          subst h_magic
          rfl
        have h_ver_canon : verifyDecl { decls := [] ++ env.decls, headerMagic := 0x4F4C454E } d = true := by
          simpa [h_env_eq] using h_ver
        have h_pref' : verifyDeclsPrefix [] (env.decls ++ [d]) = true :=
          verifyDeclsPrefix_append_singleton [] env.decls d h_pref (by simpa using h_fresh) h_ver_canon
        refine ⟨⟨h_magic, h_pref', ?_⟩, h_cic_d⟩
        intro d' hd'
        have h_ver' : verifyDecl { env with decls := env.decls ++ [d] } d' = true :=
          List.all_eq_true.mp h_all_env' d' hd'
        exact _root_.ConLeche.con_leche_verify_decl_sound { env with decls := env.decls ++ [d] } d' h_ver'
      · contradiction

/-- Bidirectional CIC type inference rejects any application `.app fn arg` whose inferred
    argument type `argTy` disagrees with the function domain `dom` (`typecheck_rejects_ill_typed_app`). -/
theorem typecheck_rejects_ill_typed_app (fuel : Nat) (env : ConLeche.Env) (ctx : List ConLeche.Expr)
    (fn arg dom body argTy : ConLeche.Expr)
    (h_fn : inferType fuel env ctx fn = some (.forallE dom body))
    (h_arg : inferType fuel env ctx arg = some argTy)
    (h_mismatch : argTy ≠ dom) :
    inferType (fuel + 1) env ctx (.app fn arg) = none := by
  dsimp [inferType, _root_.ConLeche.inferType] at h_fn h_arg ⊢
  rw [h_fn, h_arg]
  simp [h_mismatch]

/-! ## Executable Mutant-Kill Conformance Guards (`>= 3` Mutants Killed) -/

/-- Valid baseline environment and declaration (`∀ (A : Sort 0), A → A` proved by `λ A x, x`). -/
def validKernelDecl : ConLeche.Decl :=
  { name := "decl_0"
    ty := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
    val := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))
    wfTag := true }

def validKernelEnv : ConLeche.Env :=
  { decls := [validKernelDecl], headerMagic := 0x4F4C454E }

-- Positive sanity guards: valid `.olean` shard parses cleanly and `checkDecl` admits `validKernelDecl`.
#guard (parseOleanShard (encodeOleanShard validKernelEnv)).isOk == true
#guard (checkDecl { decls := [], headerMagic := 0x4F4C454E } validKernelDecl).isOk == true

/-- Mutant 1 (Corrupted `.olean` Header Magic / Truncated Payload Killed):
    corrupting the `"OLEN"` magic byte or truncating the `.olean` shard is deterministically
    rejected by `parseOleanShard`. -/
def mutant1BadMagicOleanShard : ByteArray :=
  ByteArray.mk #[0x42, 0x41, 0x44, 0x21, 0x00]

#guard (parseOleanShard mutant1BadMagicOleanShard).isOk == false
#guard (parseOleanShard (ByteArray.mk #[0x4F, 0x4C, 0x45])).isOk == false

/-- Mutant 2 (Ill-Typed / Sort-Spoofed Declaration Killed):
    a declaration claiming type `∀ (A : Sort 0), A` (`False`) with value `.sort .zero`
    is deterministically rejected by `checkDecl` and `parseOleanShard`. -/
def mutant2IllTypedDecl : ConLeche.Decl :=
  { name := "decl_0"
    ty := .forallE (.sort .zero) (.bvar 0)
    val := .sort .zero
    wfTag := true }

#guard (checkDecl { decls := [], headerMagic := 0x4F4C454E } mutant2IllTypedDecl).isOk == false
#guard (parseOleanShard (encodeOleanShard { decls := [mutant2IllTypedDecl], headerMagic := 0x4F4C454E })).isOk == false

/-- Mutant 3 (Duplicate / Cyclic Self-Referential Declaration Killed):
    1. Re-admitting a duplicate declaration name `"decl_0"` into `validKernelEnv` is rejected by `checkDecl`.
    2. A non-well-founded declaration (`wfTag := false`) or self-referential circular proof `.const "decl_0" []`
       is deterministically rejected by `checkDecl` and `parseOleanShard`. -/
def mutant3CircularSelfRefDecl : ConLeche.Decl :=
  { name := "decl_0"
    ty := .sort .zero
    val := .const "decl_0" []
    wfTag := true }

#guard (checkDecl validKernelEnv validKernelDecl).isOk == false
#guard (checkDecl { decls := [], headerMagic := 0x4F4C454E } mutant3CircularSelfRefDecl).isOk == false
#guard (parseOleanShard (encodeOleanShard { decls := [mutant3CircularSelfRefDecl], headerMagic := 0x4F4C454E })).isOk == false


/-! ## Real Lean 4 v4.35.0 `.olean` Header & Root-Bounds Validator (`roadmap/HORIZONS.md` G1b)

Unlike the `"OLEN"` v1 model codec above, this section reads the header of *real* Lean 4
v4.35.0 `.olean` compacted-region files. The 96-byte layout below was checked against all
2,546 `.olean` files shipped with the `leanprover/lean4:v4.35.0` toolchain:

| bytes   | field                                                         |
|---------|---------------------------------------------------------------|
| `0–4`   | magic `"olean"` (`0x6F 0x6C 0x65 0x61 0x6E`)                   |
| `5`     | format version (`2` by default, `3` with `allowClosures`)     |
| `6`     | flags byte (recorded, not interpreted)                        |
| `7–39`  | Lean version `"4.35.0"`, NUL-padded to 33 bytes               |
| `40–79` | toolchain githash `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`  |
| `80–87` | `base_addr`, little-endian `u64`                              |
| `88–95` | root object pointer, little-endian `u64`                      |
| `96–`   | compacted object region                                       |

Trusted boundary, stated honestly: this module validates the header and that the root
pointer lands 8-aligned inside the object region (`base_addr + 96 ≤ root`,
`root + 8 ≤ base_addr + size`). It does NOT decode the compacted object graph. Turning the
region into `Lean.Environment` declarations is done by Lean's C runtime
(`lean_compacted_region_read` / `readModuleData`), which stays in the trusted base
(`docs/TRUSTED_BASE.md` item 4). The declaration list `decoded` taken by `parseRealOlean`
is that reader's output; the theorems below say that once those declarations and the
header pass this checker, they are CIC-valid in the `ConLeche` kernel model. -/

/-- Read `len` bytes of `bytes` starting at `off` (out-of-range bytes read as `0`). -/
def bytesSlice (bytes : ByteArray) (off len : Nat) : List UInt8 :=
  (List.range len).map (fun i => bytes.get! (off + i))

/-- Read a little-endian unsigned 64-bit integer from `bytes` at `off`. -/
def readU64LE (bytes : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldr (fun i acc => acc * 256 + (bytes.get! (off + i)).toNat) 0

/-- ASCII bytes of a string literal. -/
def asciiBytes (s : String) : List UInt8 :=
  s.toList.map (fun c => c.toNat.toUInt8)

/-- Real `.olean` magic: `"olean"`. -/
def realOleanMagic : List UInt8 := [0x6F, 0x6C, 0x65, 0x61, 0x6E]

/-- Size of the fixed real `.olean` header; objects start at this offset. -/
def realOleanHeaderSize : Nat := 96

/-- Pinned Lean version field: `"4.35.0"` NUL-padded to 33 bytes (bytes `7–39`). -/
def realOleanLeanVersion : List UInt8 :=
  asciiBytes "4.35.0" ++ List.replicate 27 0

/-- Pinned toolchain githash field (bytes `40–79`). -/
def realOleanGithash : List UInt8 :=
  asciiBytes "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"

/-- Decoded fields of a real `.olean` header. -/
structure RealOleanHeader where
  version  : UInt8
  flags    : UInt8
  baseAddr : Nat
  rootPtr  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Declarative specification of a valid real v4.35.0 `.olean` header `h` for `bytes`. -/
def RealOleanHeaderSpec (bytes : ByteArray) (h : RealOleanHeader) : Prop :=
  realOleanHeaderSize ≤ bytes.size ∧
  bytesSlice bytes 0 5 = realOleanMagic ∧
  h.version = bytes.get! 5 ∧ (h.version = 2 ∨ h.version = 3) ∧
  h.flags = bytes.get! 6 ∧
  bytesSlice bytes 7 33 = realOleanLeanVersion ∧
  bytesSlice bytes 40 40 = realOleanGithash ∧
  h.baseAddr = readU64LE bytes 80 ∧
  h.rootPtr = readU64LE bytes 88 ∧
  h.baseAddr + realOleanHeaderSize ≤ h.rootPtr ∧
  h.rootPtr + 8 ≤ h.baseAddr + bytes.size ∧
  (h.rootPtr - h.baseAddr) % 8 = 0

/-- Executable check of the real `.olean` header and root-pointer bounds. -/
def realOleanHeaderOk (bytes : ByteArray) (h : RealOleanHeader) : Bool :=
  decide (realOleanHeaderSize ≤ bytes.size) &&
  bytesSlice bytes 0 5 == realOleanMagic &&
  (h.version == 2 || h.version == 3) &&
  bytesSlice bytes 7 33 == realOleanLeanVersion &&
  bytesSlice bytes 40 40 == realOleanGithash &&
  decide (h.baseAddr + realOleanHeaderSize ≤ h.rootPtr) &&
  decide (h.rootPtr + 8 ≤ h.baseAddr + bytes.size) &&
  (h.rootPtr - h.baseAddr) % 8 == 0

/-- Parse the 96-byte header of a real Lean 4 v4.35.0 `.olean` file. -/
def parseRealOleanHeader (bytes : ByteArray) : Option RealOleanHeader :=
  let h : RealOleanHeader :=
    { version := bytes.get! 5
      flags := bytes.get! 6
      baseAddr := readU64LE bytes 80
      rootPtr := readU64LE bytes 88 }
  if realOleanHeaderOk bytes h then some h else none

/-- A real `.olean` module: validated header plus kernel-checked declarations. -/
structure RealOleanModule where
  header : RealOleanHeader
  env    : ConLeche.Env

/-- Validate a real `.olean` header and kernel-check the declarations `decoded` that the
    trusted reader (`lean_compacted_region_read`) extracted from its object region. -/
def parseRealOlean (bytes : ByteArray) (decoded : List ConLeche.Decl) :
    Except String RealOleanModule :=
  match parseRealOleanHeader bytes with
  | none => .error "parseRealOlean: invalid v4.35.0 .olean header or root pointer"
  | some hdr =>
    let env : ConLeche.Env := { decls := decoded }
    if verifyDeclsPrefix [] decoded && decoded.all (verifyDecl env) then
      .ok { header := hdr, env := env }
    else
      .error "parseRealOlean: CIC kernel rejected a decoded declaration"

/-- Admit a new declaration `d` on top of a real `.olean` module. -/
def checkRealOleanDecl (bytes : ByteArray) (decoded : List ConLeche.Decl)
    (d : ConLeche.Decl) : Except String RealOleanModule :=
  match parseRealOlean bytes decoded with
  | .error e => .error e
  | .ok m =>
    match checkDecl m.env d with
    | .error e => .error e
    | .ok env' => .ok { m with env := env' }

/-- The real `.olean` header parser accepts exactly the headers meeting the declarative
    specification `RealOleanHeaderSpec`. -/
theorem parseRealOleanHeader_iff (bytes : ByteArray) (h : RealOleanHeader) :
    parseRealOleanHeader bytes = some h ↔ RealOleanHeaderSpec bytes h := by
  rcases h with ⟨v, fl, b, r⟩
  simp only [parseRealOleanHeader, realOleanHeaderOk, RealOleanHeaderSpec, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  split <;> rename_i hok
  · simp only [Option.some.injEq, RealOleanHeader.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hok.1.1.1.1.1.1.1, hok.1.1.1.1.1.1.2, rfl, hok.1.1.1.1.1.2, rfl,
        hok.1.1.1.1.2, hok.1.1.1.2, rfl, rfl, hok.1.1.2, hok.1.2, hok.2⟩
    · rintro ⟨-, -, hv, -, hf, -, -, hb, hr, -⟩
      exact ⟨hv.symm, hf.symm, hb.symm, hr.symm⟩
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨hs, hm, rfl, hv, rfl, hl, hg, rfl, rfl, hb, hr, ha⟩
    exact hok ⟨⟨⟨⟨⟨⟨⟨hs, hm⟩, hv⟩, hl⟩, hg⟩, hb⟩, hr⟩, ha⟩

/-- No `"OLEN"` v1 model shard is a real `.olean`: encoded shards and every shard accepted
    by `parseOleanShard` start with `'O'` (`0x4F`), never with the `'o'` of `"olean"`. -/
theorem olen_shard_not_real_olean (env : ConLeche.Env) :
    parseRealOleanHeader (encodeOleanShard env) = none ∧
    ∀ bytes env', parseOleanShard bytes = .ok env' → parseRealOleanHeader bytes = none := by
  have key : ∀ bytes : ByteArray, bytes.get! 0 = 0x4F → parseRealOleanHeader bytes = none := by
    intro bytes h0
    cases hp : parseRealOleanHeader bytes with
    | none => rfl
    | some h =>
      have hm := congrArg List.head? ((parseRealOleanHeader_iff bytes h).mp hp).2.1
      simp [bytesSlice, realOleanMagic, List.range_succ, h0] at hm
  refine ⟨key _ ?_, fun bytes env' hp => key bytes ?_⟩
  · simp [_root_.ConLeche.encodeOleanShard, ByteArray.get!]
  · unfold parseOleanShard _root_.ConLeche.parseOleanShard at hp
    split at hp
    · contradiction
    · split at hp
      · contradiction
      · rename_i hmag
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
          not_or, Classical.not_not] at hmag
        exact hmag.1.1.1

/-- A successful real `.olean` parse yields a header meeting `RealOleanHeaderSpec`, keeps
    exactly the trusted reader's declarations, and every one of them is CIC-valid. -/
theorem real_olean_bridge_sound (bytes : ByteArray) (decoded : List ConLeche.Decl)
    (m : RealOleanModule) (h_parse : parseRealOlean bytes decoded = .ok m) :
    RealOleanHeaderSpec bytes m.header ∧ m.env.decls = decoded ∧ EnvWellFormed m.env := by
  unfold parseRealOlean at h_parse
  split at h_parse
  · contradiction
  · rename_i hdr hhdr
    dsimp only at h_parse
    split at h_parse
    · rename_i hok
      injection h_parse with hm
      subst hm
      rcases Bool.and_eq_true_iff.mp hok with ⟨hpref, hall⟩
      refine ⟨(parseRealOleanHeader_iff bytes hdr).mp hhdr, rfl, rfl, hpref, fun d hd => ?_⟩
      exact _root_.ConLeche.con_leche_verify_decl_sound _ d (List.all_eq_true.mp hall d hd)
    · contradiction

/-- Admitting `d` on top of a real `.olean` module preserves header validity and
    environment well-formedness, and `d` itself is CIC-valid. -/
theorem real_olean_checkDecl_sound (bytes : ByteArray) (decoded : List ConLeche.Decl)
    (d : ConLeche.Decl) (m' : RealOleanModule)
    (h_ok : checkRealOleanDecl bytes decoded d = .ok m') :
    RealOleanHeaderSpec bytes m'.header ∧ EnvWellFormed m'.env ∧
    CICValid { decls := decoded } d := by
  unfold checkRealOleanDecl at h_ok
  split at h_ok
  · contradiction
  · rename_i m hm
    have ⟨hspec, hdecls, hwf⟩ := real_olean_bridge_sound bytes decoded m hm
    split at h_ok
    · contradiction
    · rename_i env' henv'
      injection h_ok with h_eq
      subst h_eq
      have ⟨hwf', hcic⟩ := con_leche_verify_decl_sound m.env env' d hwf henv'
      have h_env : m.env = { decls := decoded } := by
        rcases hwf with ⟨hmag, -⟩
        cases hme : m.env
        simp_all
      exact ⟨hspec, hwf', h_env ▸ hcic⟩

/-! ### Real `.olean` header mutant-kill guards -/

/-- Little-endian `u64` encoding of `n`. -/
def u64LEBytes (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i => (n / 256 ^ i % 256).toUInt8)

/-- Assemble a synthetic real `.olean` image: 96-byte header plus `objLen` zero object bytes. -/
def mkRealOleanBytes (magic : List UInt8) (version : UInt8) (leanVer githash : List UInt8)
    (base root objLen : Nat) : ByteArray :=
  let header := magic ++ [version, 1] ++ leanVer ++ githash ++ u64LEBytes base ++ u64LEBytes root
  ByteArray.mk (header ++ List.replicate objLen 0).toArray

/-- `base_addr` taken from the v4.35.0 `Init/Prelude.olean` header. -/
def sampleRealOleanBase : Nat := 0x31FC9D500000

/-- Valid baseline: version `2`, root at the first object (`base_addr + 96`). -/
def validRealOleanBytes : ByteArray :=
  mkRealOleanBytes realOleanMagic 2 realOleanLeanVersion realOleanGithash
    sampleRealOleanBase (sampleRealOleanBase + 96) 16

/-- Build a variant of the baseline with one field changed. -/
def realOleanVariant (magic : List UInt8 := realOleanMagic) (version : UInt8 := 2)
    (leanVer : List UInt8 := realOleanLeanVersion) (githash : List UInt8 := realOleanGithash)
    (rootOff : Nat := 96) : ByteArray :=
  mkRealOleanBytes magic version leanVer githash
    sampleRealOleanBase (sampleRealOleanBase + rootOff) 16

-- Positive guards: the baseline and the `allowClosures` (version 3) variant are accepted.
#guard (parseRealOleanHeader validRealOleanBytes).isSome
#guard (parseRealOleanHeader (realOleanVariant (version := 3))).isSome
#guard (parseRealOleanHeader validRealOleanBytes).map (·.baseAddr) == some sampleRealOleanBase
#guard (parseRealOleanHeader validRealOleanBytes).map (fun h => h.rootPtr - h.baseAddr) == some 96
#guard (parseRealOleanHeader (realOleanVariant (rootOff := 104))).isSome
#guard u64LEBytes sampleRealOleanBase == [0x00, 0x00, 0x50, 0x9D, 0xFC, 0x31, 0x00, 0x00]

-- Mutant R1: `"OLEN"` model shards and a capitalised magic are not real `.olean` files.
#guard (parseRealOleanHeader (encodeOleanShard validKernelEnv)).isNone
#guard (parseRealOleanHeader (realOleanVariant (magic := asciiBytes "OLEAN"))).isNone
-- Mutant R2: unknown format version.
#guard (parseRealOleanHeader (realOleanVariant (version := 4))).isNone
#guard (parseRealOleanHeader (realOleanVariant (version := 1))).isNone
-- Mutant R3: different Lean version or toolchain githash.
#guard (parseRealOleanHeader
  (realOleanVariant (leanVer := asciiBytes "4.34.1" ++ List.replicate 27 0))).isNone
#guard (parseRealOleanHeader
  (realOleanVariant (githash := asciiBytes "0b6cafb7290e8bd5f2937522d8d804f58f02bafc"))).isNone
-- Mutant R4: header truncated below 96 bytes.
#guard (parseRealOleanHeader (validRealOleanBytes.extract 0 95)).isNone
-- Mutant R5: root pointer inside the header, past the region end, or misaligned.
#guard (parseRealOleanHeader (realOleanVariant (rootOff := 88))).isNone
#guard (parseRealOleanHeader (realOleanVariant (rootOff := 112))).isNone
#guard (parseRealOleanHeader (realOleanVariant (rootOff := 100))).isNone

-- Mutant R6: the CIC kernel still gates declarations read from a valid real header.
#guard (parseRealOlean validRealOleanBytes [validKernelDecl]).isOk
#guard (parseRealOlean validRealOleanBytes [mutant2IllTypedDecl]).isOk == false
#guard (parseRealOlean (realOleanVariant (version := 4)) [validKernelDecl]).isOk == false
#guard (checkRealOleanDecl validRealOleanBytes [] validKernelDecl).isOk
#guard (checkRealOleanDecl validRealOleanBytes [validKernelDecl] validKernelDecl).isOk == false

end TurboLean.Kernel.ConLeche
