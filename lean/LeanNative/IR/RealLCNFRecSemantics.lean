import LeanNative.IR.RealLCNFSemantics

/-!
# Fuel-Indexed Recursion-Capable Real-LCNF Evaluator (`evalStepR`) — rung L3

The L3 extension of `evalStep` with a declaration environment whose local calls are
FUEL-INDEXED over the FULL environment (L3 contract, `Proofs/LowerRec.lean`): on a
`.let` whose value is a `.fap` to a `ctx`-local callee, the callee declaration is looked
up in the WHOLE `Δ` — whose entries PAIR each declaration with its own `RealBridgeCtx`,
because the driver builds a per-declaration context (the contract's amendment note) —
and its body runs at the step's decremented fuel under that paired context, so self and
mutual recursion evaluate, bounded by the step budget `evalStep` already carries. The
caller's `ctx` binder governs only the caller's own clauses. A lookup miss
errors `.unsupportedCall` byte-for-byte like the old semantics, so `Δ = []` is the old
evaluator by theorem (`evalStepR_nil`, `Proofs/LowerRec.lean`).

This file is NEW and imports `LeanNative.IR.RealLCNFSemantics` only, preserving the H1.1
separation pin (`Tests/RealLCNFSeparationPin.lean`): nothing here imports the lowerer.
It does not touch the L2 lane's planned `IR/RealLCNFCallSemantics.lean` or its names.
-/

namespace LeanNative.IR.RealLCNFSemantics

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.Semantics

/-- First entry whose declaration's `.name` is `fn`. The hit alone (no stratified
    suffix), paired with the callee's own lowering context — the callee re-runs under
    the same full `Δ`, which is what admits self and mutual recursion. -/
def lookupDeclRec? : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx) → Lean.Name →
    Option (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)
  | [], _ => none
  | e :: Δ, fn => if e.1.name == fn then some e else lookupDeclRec? Δ fn

/-- A `lookupDeclRec?` hit is a member entry whose declaration has that name. -/
theorem lookupDeclRec?_mem : ∀ (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx))
    (fn : Lean.Name) (e : Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx),
    lookupDeclRec? Δ fn = some e → e ∈ Δ ∧ e.1.name = fn
  | [], _, _, h => nomatch h
  | e0 :: Δ, fn, e, h => by
    dsimp only [lookupDeclRec?] at h
    split at h
    · next hb =>
      injection h with h'
      subst h'
      exact ⟨List.mem_cons_self .., eq_of_beq hb⟩
    · next =>
      have ⟨hm, hn⟩ := lookupDeclRec?_mem Δ fn e h
      exact ⟨List.mem_cons_of_mem _ hm, hn⟩

/-- Verbatim mirror of `evalStep`'s stored-type / active-constructor computation for a
    `.let` binding (the `storedTy`/`storedCtor` block), factored so `evalStepR` states it
    once; `evalStepR_nil` (`Proofs/LowerRec.lean`) proves it against the inline block. -/
def letStoredR (ctx : RealBridgeCtx) (env : LEnv)
    (declVal : Lean.Compiler.LCNF.LetValue .impure) (rawTy : LNIRType)
    (ctor? : Option Lean.Name) : LNIRType × Option Lean.Name :=
  let storedTy : LNIRType := match declVal with
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
  let storedCtor : Option Lean.Name := match declVal with
    | .ctor _ _ _ => if lnirTypeEq storedTy .objPtr then ctor? else none
    | _ => none
  (storedTy, storedCtor)

/-- Fuel-indexed recursion-capable step evaluator (L3 contract, `Proofs/LowerRec.lean`):
    mirrors `evalStep` clause for clause (same fuel-structural recursion, same
    `evalLetValue`, same stored-type machinery via `letStoredR`, same join-point,
    `cases`, rc and mutation handling, every recursive occurrence at the step's
    decremented fuel, the same `Δ` and — on the caller's own clauses — the same `ctx`)
    with ONE new rule, replacing exactly the arm the old semantics deliberately errors
    on: a `.let` whose value is a `.fap` to a `ctx`-local callee resolves the callee in
    the FULL `Δ` and runs its body at the decremented fuel under the CALLEE'S OWN paired
    context and the declaration-entry binding convention; a lookup miss is
    `.error (.unsupportedCall ...)` byte-for-byte like `evalLetValue`. -/
def evalStepR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) (fuel : Nat)
    (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
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
        evalStepR Δ fuel ctx env st (.inl code)
      | [.ctorAlt info code _] =>
        let envIn := match discr? with
          | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
          | none => env
        evalStepR Δ fuel ctx envIn st (.inl code)
      | alt :: rest =>
        match alt with
        | .default code => evalStepR Δ fuel ctx env st (.inl code)
        | .ctorAlt info code _ =>
          let envIn := match discr? with
            | some dx => if (env.vals dx).isSome then env.withCtor dx info.name else env
            | none => env
          if isBool then
            match asBool cond with
            | .ok b =>
              if info.cidx == 0 then
                if b then evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStepR Δ fuel ctx envIn st (.inl code)
              else if info.cidx == 1 then
                if b then evalStepR Δ fuel ctx envIn st (.inl code)
                else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == info.cidx.toUInt64 then evalStepR Δ fuel ctx envIn st (.inl code)
              else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
        | .alt ctorName _ code _ =>
          let cidx := (ctx.findNullaryCtor? ctorName).getD idx
          if isBool then
            match asBool cond with
            | .ok b =>
              if cidx == 0 then
                if b then evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
                else evalStepR Δ fuel ctx env st (.inl code)
              else if cidx == 1 then
                if b then evalStepR Δ fuel ctx env st (.inl code)
                else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
              else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | .error e => .error e
          else
            match cond with
            | .u64 n =>
              if n == cidx.toUInt64 then evalStepR Δ fuel ctx env st (.inl code)
              else evalStepR Δ fuel ctx env st (.inr (cond, isBool, idx + 1, discr?, rest))
            | _ => .error (.typeError "evalBinOp: invalid operand types")
    | .inl code =>
      match code with
      | .let decl k =>
        let rawTy := lowerGroundImpureTypeWith ctx decl.type
        match decl.value with
        | .fap fn args _ =>
          if (ctx.findLocalCallee? fn).isSome then
            match lookupDeclRec? Δ fn with
            | some (sd, sdCtx) =>
              match evalArgs env.vals args.toList with
              | .error e => .error e
              | .ok vals =>
                match sd.value with
                | .extern _ => .error (.unsupportedCall fn.toString)
                | .code c =>
                  match bindParams sdCtx true LEnv.empty sd.params.toList vals with
                  | .error e => .error e
                  | .ok env' =>
                    match evalStepR Δ fuel sdCtx env' st (.inl c) with
                    | .error e => .error e
                    | .ok (v, st') =>
                      evalStepR Δ fuel ctx
                        (env.bind decl.fvarId v none
                          (some (if isUnboxedScalarOrTuple rawTy then rawTy else .i64)))
                        st' (.inl k)
            | none => .error (.unsupportedCall fn.toString)
          else
            match evalLetValue ctx env st decl.value rawTy with
            | .ok (v, st', ctor?) =>
              evalStepR Δ fuel ctx
                (env.bind decl.fvarId v (letStoredR ctx env decl.value rawTy ctor?).2
                  (some (letStoredR ctx env decl.value rawTy ctor?).1))
                st' (.inl k)
            | .error e => .error e
        | _ =>
          match evalLetValue ctx env st decl.value rawTy with
          | .ok (v, st', ctor?) =>
            evalStepR Δ fuel ctx
              (env.bind decl.fvarId v (letStoredR ctx env decl.value rawTy ctor?).2
                (some (letStoredR ctx env decl.value rawTy ctor?).1))
              st' (.inl k)
          | .error e => .error e
      | .inc x n _ _ k _ =>
        match applyRc true env st x n with
        | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
        | .error e => .error e
      | .dec x n _ _ _ k _ =>
        match applyRc false env st x n with
        | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
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
          | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | some (.sarrayId bufId) =>
          let stepRes :=
            if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
            else if isHeapTy then st.decRefBuf bufId 1
            else .ok st
          match stepRes with
          | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
          | .error e => .error e
        | some _ =>
          if ctx.allowStage1DHeap && isHeapTy then .error (.typeError "lean_native_del_obj expects (objPtr)")
          else evalStepR Δ fuel ctx env st (.inl k)
        | none =>
          if isHeapTy then .error (.unboundVar 0)
          else evalStepR Δ fuel ctx env st (.inl k)
      | .setTag x cidx k _ =>
        match env.vals x with
        | some (.objPtr objId) =>
          let nextCtor? := match env.resolveCtor? ctx x with
            | some cur =>
              if ctx.hasSiblingEntry cur then ctx.findSiblingCtor? cur cidx
              else none
            | none => none
          match st.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
          | .ok st' => evalStepR Δ fuel ctx (env.withCtorOpt x nextCtor?) st' (.inl k)
          | .error e => .error e
        | none => .error (.unboundVar 0)
        | _ => .error (.typeError "lean_native_ctor_set_tag expects (objPtr, u64)")
      | .oset x i y k _ =>
        if !env.isHeapVar x then evalStepR Δ fuel ctx env st (.inl k)
        else match env.vals x with
        | some (.objPtr objId) =>
          match evalArg env.vals y with
          | .ok v =>
            match writeField st objId (i.toUInt64).toNat v true with
            | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
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
          | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
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
          | .ok st' => evalStepR Δ fuel ctx env st' (.inl k)
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
            | .ok tag => evalStepR Δ fuel ctx env st (.inr (tag, false, 0, some c.discr, ordered))
            | .error e => .error e
          else
            let isBool := c.typeName == ``Bool || lnirTypeEq ((env.tys c.discr).getD .objPtr) .i1
            evalStepR Δ fuel ctx env st (.inr (v, isBool, 0, none, ordered))
      | .return x =>
        match env.vals x with | some v => .ok (v, st) | none => .error (.unboundVar 0)
      | .unreach _ => .error (.typeError "reached unreachable code")
      | .jp decl k =>
        if hasJmpToPure fuel decl.fvarId (.inl decl.value) then
          .error (.unsupportedCall "recursive join point")
        else
          let env' := env.bindJp decl.fvarId { params := decl.params.toList, code := decl.value }
          evalStepR Δ fuel ctx env' st (.inl k)
      | .jmp fvarId args =>
        match env.jps fvarId with
        | none => .error (.unsupportedCall "unmapped join point")
        | some body =>
          match evalJpArgs env.vals args.toList with
          | .error e => .error e
          | .ok vs =>
            match bindJpParams ctx env.tys env body.params args.toList vs with
            | .ok env' => evalStepR Δ fuel ctx env' st (.inl body.code)
            | .error e => .error e
      | .fun decl _ _ => .error (.unsupportedCall s!"local function {decl.binderName}")

/-- Mirror of `evalRealLCNFCode` over `evalStepR`. -/
def evalRealLCNFCodeR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) (fuel : Nat)
    (ctx : RealBridgeCtx) (env : LEnv) (st : HeapState)
    (code : Lean.Compiler.LCNF.Code .impure) : Except UBError (Val × HeapState) :=
  evalStepR Δ fuel ctx env st (.inl code)

/-- Mirror of `evalRealLCNFDecl` over `evalStepR`: `Δ` may hold `decl` itself, paired
    with its own context (the driver's `localCallees` includes the self name), which is
    what makes self and mutual recursion run. -/
def evalRealLCNFDeclR (Δ : List (Lean.Compiler.LCNF.Decl .impure × RealBridgeCtx)) (fuel : Nat)
    (ctx : RealBridgeCtx) (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val)
    (st : HeapState := HeapState.empty) : Except UBError (Val × HeapState) :=
  match decl.value with
  | .extern _ => .error (.unsupportedCall s!"extern {decl.name}")
  | .code c =>
    match bindParams ctx true LEnv.empty decl.params.toList args with
    | .ok env => evalRealLCNFCodeR Δ fuel ctx env st c
    | .error e => .error e

end LeanNative.IR.RealLCNFSemantics
