import LeanNative.IR.RealLCNFSemantics

/-!
# L2 (roadmap H1 rung L2 "Calls"): function environment for the real-LCNF semantics

Contract: `lean/LeanNative/Proofs/LowerCalls.lean`. This is a NEW file (rather than an
append to `IR/RealLCNFSemantics.lean`) because `scripts/lcnf_coverage_results.json`
sha-pins that file; it imports `LeanNative.IR.RealLCNFSemantics` only, so the H1.1
separation pin (`Tests/RealLCNFSeparationPin.lean`) is preserved: nothing here touches
the lowerer module.

Each environment entry carries its declaration's OWN `RealBridgeCtx` and fuel: the driver
builds a separate context per declaration (`paramTypeMap`, `allowStage1DHeap`,
`ctorLayouts`, `typeOverrides` are per-declaration), so a callee evaluated under the
CALLER's context would describe a module the driver never emits (the concrete failure: a
callee `uset`/`sset` on a constructor the caller never mentions falls back to the raw
slot index). The call rule therefore runs the callee under the entry's own context and
fuel, and `DeclEnvLowers` requires the per-entry lowering
`lowerRealLCNFDecl fuel_i ctx_i sd ld.name = .ok ld`.

`evalStepF` mirrors `evalStep` clause for clause (same `evalLetValue`, same
`storedTy`/`storedCtor` machinery, same join-point and `cases` handling, recursive
occurrences at the same `Δ` and ambient `ctx`) with ONE new rule, replacing exactly the
arm the old semantics deliberately errors on: a `.let` whose value is `.fap fn args _`
with `(ctx.findLocalCallee? fn).isSome` (the CALL SITE's gate is the caller's map — the
map the lowerer consulted when it emitted the call) and `fn` bound in `Δ` runs the callee
declaration under the entry's own context and fuel and the strict suffix. On a lookup
miss the arm keeps the old `.error (.unsupportedCall fn.toString)` byte for byte, so
`Δ = []` is the old semantics (`evalStepF_nil`, proved in `LowerCalls.lean`). The
environment is stratified: a call resolves only against strictly later entries, and in
the environments `DeclEnvLowers` admits (pairwise-fresh names) a self or backward call
misses; with duplicate names in `Δ` a self-call can resolve once against a later entry.
Termination is lexicographic on `(Δ.length, fuel)`: every mirrored recursion keeps `Δ`
and decrements the ambient fuel, and the call rule strictly shrinks the environment.
-/

namespace LeanNative.IR.RealLCNFSemantics

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.Semantics

/-- Source-side function environment: the LCNF declarations a local call may resolve
    against, in dependency order (callees strictly later than callers), each with its
    OWN lowering/evaluation context and fuel. -/
abbrev DeclEnv := List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat)

namespace DeclEnv

/-- First entry whose declaration is named `fn`, paired with the strict suffix after it. -/
def lookup? : DeclEnv → Lean.Name →
    Option ((Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) × DeclEnv)
  | [], _ => none
  | p :: Δ, fn => if p.1.name == fn then some (p, Δ) else lookup? Δ fn

theorem lookup?_length : ∀ (Δ : DeclEnv) (fn : Lean.Name)
    (p : Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) (Δ' : DeclEnv),
    lookup? Δ fn = some (p, Δ') → Δ'.length < Δ.length := by
  intro Δ
  induction Δ with
  | nil => intro fn p Δ' h; exact nomatch h
  | cons p0 Δ ih =>
    intro fn p Δ' h
    unfold lookup? at h
    split at h
    · injection h with h
      cases h
      exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (ih fn p Δ' h)

/-- The local-call view of a let-bound value: callee entry (declaration, its own context
    and fuel), strict suffix, and arguments, when the value is `.fap fn args _`, the
    CALLER's mangled-name map knows `fn` (`ctx.findLocalCallee?` — the map the lowerer
    consulted at this call site), and `fn` is bound in `Δ`. `none` for every other
    value — those keep `evalLetValue`'s behavior, including its deliberate
    `.unsupportedCall` error when `findLocalCallee?` hits but `Δ` misses. -/
def callTarget? (Δ : DeclEnv) (ctx : RealBridgeCtx) :
    Lean.Compiler.LCNF.LetValue .impure →
    Option ((Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat) × DeclEnv ×
      Array (Lean.Compiler.LCNF.Arg .impure))
  | .fap fn args _ =>
    match lookup? Δ fn with
    | some (p, Δ') =>
      if (ctx.findLocalCallee? fn).isSome then some (p, Δ', args) else none
    | none => none
  | _ => none

theorem callTarget?_length {Δ : DeclEnv} {ctx : RealBridgeCtx}
    {lv : Lean.Compiler.LCNF.LetValue .impure}
    {p : Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx × Nat} {Δ' : DeclEnv}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    (h : callTarget? Δ ctx lv = some (p, Δ', args)) : Δ'.length < Δ.length :=
  -- `cases lv` cannot build the dependent elimination here ("Missing cases: _"), so
  -- enumerate the constructors of `LetValue .impure` by hand; every non-`fap` arm
  -- reduces `callTarget?` to `none`, refuting `h`. A `_` catch-all would keep
  -- `callTarget?` stuck, so the enumeration is explicit.
  match lv, h with
  | .lit _, h => nomatch h
  | .erased, h => nomatch h
  | .proj _ _ _ hpu, _ => nomatch hpu
  | .const _ _ _ hpu, _ => nomatch hpu
  | .fvar _ _, h => nomatch h
  | .ctor _ _ _, h => nomatch h
  | .oproj _ _ _, h => nomatch h
  | .uproj _ _ _, h => nomatch h
  | .sproj _ _ _ _, h => nomatch h
  | .pap _ _ _, h => nomatch h
  | .reset _ _ _, h => nomatch h
  | .reuse _ _ _ _ _, h => nomatch h
  | .box _ _ _, h => nomatch h
  | .unbox _ _, h => nomatch h
  | .isShared _ _, h => nomatch h
  | .fap fn args0 _, h => by
    -- `unfold` leaves the outer matcher un-iota-reduced (our `fn` shadowed by the
    -- arm binder); `simp only [callTarget?]` reduces it on the literal `.fap`.
    simp only [callTarget?] at h
    match hl : lookup? Δ fn with
    | none => rw [hl] at h; exact nomatch h
    | some (p0, Δ0) =>
      rw [hl] at h
      simp only at h  -- iota-reduce the matcher on the literal `some (p0, Δ0)`
      split at h
      · injection h with h
        cases h
        exact lookup?_length Δ _ _ _ hl
      · exact nomatch h

end DeclEnv

set_option linter.unusedVariables false in
/-- L2 environment-aware real-LCNF step evaluation (see the module docstring). -/
def evalStepF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (Val × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure))) :
    Except UBError (Val × HeapState) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
    match target with
    | .inr (cond, isBool, idx, discr?, alts) =>
      match alts with
      | [] => .error (.typeError "reached unreachable code")
      | [.alt _ _ code _] | [.default code] =>
        evalStepF Δ fuel ctx env st (.inl code)
      | [.ctorAlt info code _] =>
        let envIn := match discr? with
          | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
          | none => env
        evalStepF Δ fuel ctx envIn st (.inl code)
      | alt :: rest =>
        match alt with
        | .default code => evalStepF Δ fuel ctx env st (.inl code)
        | .ctorAlt info code _ =>
          let envIn := match discr? with
            | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
            | none => env
          if isBool then
            match asBool cond with
            | .ok b =>
              if info.cidx == 0 then
                if b then evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStepF Δ fuel ctx envIn st (.inl code)
              else if info.cidx == 1 then
                if b then evalStepF Δ fuel ctx envIn st (.inl code)
                else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == info.cidx.toUInt64 then evalStepF Δ fuel ctx envIn st (.inl code)
              else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
        | .alt ctorName _ code _ =>
          let cidx := (ctx.findNullaryCtor? ctorName).getD idx
          if isBool then
            match asBool cond with
            | .ok b =>
              if cidx == 0 then
                if b then evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStepF Δ fuel ctx env st (.inl code)
              else if cidx == 1 then
                if b then evalStepF Δ fuel ctx env st (.inl code)
                else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == cidx.toUInt64 then evalStepF Δ fuel ctx env st (.inl code)
              else evalStepF Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
    | .inl code =>
      match code with
      | .let decl k =>
        let rawTy := lowerGroundImpureTypeWith ctx decl.type
        match hc : DeclEnv.callTarget? Δ ctx decl.value with
        | some ((sd, ctxD, fuelD), Δ', args) =>
          match evalArgs env.vals args.toList with
          | .error e => .error e
          | .ok vals =>
            match bindParams ctxD true LEnv.empty sd.params.toList vals with
            | .error e => .error e
            | .ok envCallee =>
              match sd.value with
              | .extern _ => .error (.unsupportedCall s!"extern {sd.name}")
              | .code c =>
                match evalStepF Δ' fuelD ctxD envCallee st (.inl c) with
                | .error e => .error e
                | .ok (v, st') =>
                  let storedTy := if isUnboxedScalarOrTuple rawTy then rawTy else .i64
                  evalStepF Δ fuel ctx (env.bind decl.fvarId v none (some storedTy)) st' (.inl k)
        | none =>
          match evalLetValue ctx env st decl.value rawTy with
          | .ok (v, st', ctor?) =>
            let storedTy := match decl.value with
              | .ctor info args _ | .reuse _ info _ args _ =>
                if ctor?.isSome then .objPtr
                else if args.isEmpty then (if isUnboxedScalarOrTuple rawTy then rawTy else .i64)
                else match ctx.findTupleArity? info.name with
                  | some numFields =>
                    let dropCnt := if args.size > numFields then args.size - numFields else 0
                    .tuple ((args.toList.drop dropCnt).map fun
                      | .fvar x => (env.tys x).getD .objPtr
                      | _ => .objPtr)
                  | none => rawTy
              | .box _ x _ =>
                let sty := (env.tys x).getD .objPtr
                if isUnboxedScalarOrTuple sty then sty else .i64
              | .fvar x _ | .unbox x _ | .reset _ x _ =>
                let sty := (env.tys x).getD .objPtr
                if isUnboxedScalarOrTuple rawTy then rawTy
                else if isUnboxedScalarOrTuple sty then sty else rawTy
              | .oproj idx x _ =>
                match (env.tys x).getD .objPtr with
                | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
                | _ => rawTy
              | .uproj idx x _ =>
                match (env.tys x).getD .objPtr with
                | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[idx]?.getD .i64
                | _ => rawTy
              | .sproj _ off x _ =>
                match (env.tys x).getD .objPtr with
                | .tuple fs => if isUnboxedScalarOrTuple rawTy then rawTy else fs[off]?.getD .i64
                | _ => rawTy
              | .isShared x _ =>
                if isUnboxedScalarOrTuple ((env.tys x).getD .objPtr) then
                  if isUnboxedScalarOrTuple rawTy then rawTy else .i64
                else .i1
              | .lit _ | .erased =>
                if isUnboxedScalarOrTuple rawTy then rawTy else .i64
              | .fap _ _ _ =>
                if isUnboxedScalarOrTuple rawTy then rawTy else .i64
              | .pap _ _ _ => rawTy
            let storedCtor := match decl.value with
              | .ctor _ _ _ => if lnirTypeEq storedTy .objPtr then ctor? else none
              | _ => none
            evalStepF Δ fuel ctx (env.bind decl.fvarId v storedCtor (some storedTy)) st' (.inl k)
          | .error e => .error e
      | .inc x n _ _ k _ =>
        match applyRc true env st x n with
        | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
        | .error e => .error e
      | .dec x n _ _ _ k _ =>
        match applyRc false env st x n with
        | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
        | .error e => .error e
      | .del x k _ =>
        let isHeapTy := env.isHeapVar x
        match env.vals x with
        | some (.objPtr objId) =>
          let stepRes :=
            if ctx.allowStage1DHeap && isHeapTy then st.delObjShell objId
            else if isHeapTy then st.decRefObj objId 1
            else .ok st
          match stepRes with
          | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | some (.sarrayId bufId) =>
          let stepRes :=
            if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
            else if isHeapTy then st.decRefBuf bufId 1
            else .ok st
          match stepRes with
          | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | some _ =>
          if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
          else evalStepF Δ fuel ctx env st (.inl k)
        | none =>
          if isHeapTy then .error (.unboundVar 0)
          else evalStepF Δ fuel ctx env st (.inl k)
      | .setTag x cidx k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          let nextCtor? := match env.resolveCtor? ctx x with
            | some cur =>
              if ctx.hasSiblingEntry cur then ctx.findSiblingCtor? cur cidx
              else none
            | none => none
          match st.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
          | .ok st' => evalStepF Δ fuel ctx (env.withCtorOpt x nextCtor?) st' (.inl k)
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | _ => .error (.typeError "lean_native_ctor_set_tag expects (objPtr, u64)")
      | .oset x i y k _ =>
        if !env.isHeapVar x then evalStepF Δ fuel ctx env st (.inl k)
        else match env.vals x with
        | some (.objPtr objId) =>
          match evalArg env.vals y with
          | .ok v =>
            match writeField st objId (i.toUInt64).toNat v true with
            | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
            | .error e => .error e
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | some _ =>
          match evalArg env.vals y with
          | .ok _ => .error (.typeError "lean_native_ctor_set expects (objPtr, u64, val)")
          | .error e => .error e
      | .uset x i y k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? i) with
            | some (s, _) => s
            | none => i
          match writeField st objId (slot.toUInt64).toNat v false with
          | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "lean_native_ctor_set_scalar expects (objPtr, u64, val)")
      | .sset x n off y _ k _ =>
        match env.vals x, env.vals y with
        | some (.objPtr objId), some v =>
          let slot := match env.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? n off) with
            | some (s, _) => s
            | none => off
          match writeField st objId (slot.toUInt64).toNat v false with
          | .ok st' => evalStepF Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | none, _ | _, none => .error (.unboundVar 0)
        | _, _ => .error (.typeError "lean_native_ctor_set_scalar expects (objPtr, u64, val)")
      | .cases c =>
        match env.vals c.discr with
        | none => .error (.unboundVar 0)
        | some v =>
          let ordered := orderAltsPure c.alts.toList
          if (ctx.allowStage1DHeap || c.typeName == ``Bool) && env.isHeapVar c.discr then
            match tagOf v st with
            | .ok tag => evalStepF Δ fuel ctx env st (.inr (tag, false, 0, some c.discr, ordered))
            | .error e => .error e
          else
            let isBool := c.typeName == ``Bool || lnirTypeEq ((env.tys c.discr).getD .objPtr) .i1
            evalStepF Δ fuel ctx env st (.inr (v, isBool, 0, none, ordered))
      | .return x =>
        match env.vals x with | some v => .ok (v, st) | none => .error (.unboundVar 0)
      | .unreach _ => .error (.typeError "reached unreachable code")
      | .jp decl k =>
        if hasJmpToPure fuel decl.fvarId (.inl decl.value) then
          .error (.unsupportedCall "recursive join point")
        else
          let env' := env.bindJp decl.fvarId { params := decl.params.toList, code := decl.value }
          evalStepF Δ fuel ctx env' st (.inl k)
      | .jmp fvarId args =>
        match env.jps fvarId with
        | none => .error (.unsupportedCall "unmapped join point")
        | some body =>
          match evalJpArgs env.vals args.toList with
          | .error e => .error e
          | .ok vs =>
            match bindJpParams ctx env.tys env body.params args.toList vs with
            | .ok env' => evalStepF Δ fuel ctx env' st (.inl body.code)
            | .error e => .error e
      | .fun decl _ _ => .error (.unsupportedCall s!"local function {decl.binderName}")
termination_by (Δ.length, fuel)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (DeclEnv.callTarget?_length hc)
    | (apply Prod.Lex.right; simp +arith)

/-- L2 environment-aware mirror of `evalRealLCNFCode`. -/
def evalRealLCNFCodeF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx) (env : LEnv)
    (st : HeapState) (code : Lean.Compiler.LCNF.Code .impure) :
    Except UBError (Val × HeapState) :=
  evalStepF Δ fuel ctx env st (.inl code)

/-- L2 environment-aware mirror of `evalRealLCNFDecl`. -/
def evalRealLCNFDeclF (Δ : DeclEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val)
    (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState) :=
  match decl.value with
  | .extern _ => .error (.unsupportedCall s!"extern {decl.name}")
  | .code c =>
    match bindParams ctx true LEnv.empty decl.params.toList args with
    | .ok env => evalRealLCNFCodeF Δ fuel ctx env st c
    | .error e => .error e

end LeanNative.IR.RealLCNFSemantics
