/-
  TurboLean.ConLeche (Milestone M2):
  Self-contained dependent Calculus of Inductive Constructions (CIC) kernel (`ConLeche`)
  with universe levels (`zero`, `succ`, `max`, `imax`, `param`), de Bruijn lifting &
  capture-avoiding substitution (`lift`, `subst`, `inst0`), fuel-bounded WHNF & definitional
  equality (`whnf`, `isDefEq`), inductive typing judgment (`HasType`), bidirectional
  typechecker (`inferType`, `verifyDecl`), and binary `.olean` declaration shard parser/encoder
  (`parseOleanShard`, `encodeOleanShard`).
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

/-- Parse and type-check a binary `.olean` shard (`bytes : ByteArray`):
    1. Verifies minimum header size (`bytes.size ≥ 5`) and `"OLEN"` magic (`0x4F, 0x4C, 0x45, 0x4E`).
    2. Reads `declCount = (bytes.get! 4).toNat`, decodes `declCount` binary declarations, and verifies exact byte consumption (`offEnd == bytes.size`).
    3. Verifies acyclic incremental prefix typing (`verifyDeclsPrefix [] decls`) and full-environment typing (`decls.all (verifyDecl env)`). -/
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
