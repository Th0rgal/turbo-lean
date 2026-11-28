import LeanNative.Proofs.RealLCNFBridge.StepMono

/-!
# W2-L2: call tables in the `RealLCNFSemantics → LNIR` simulation (`CallTable.lean`)

`FuncsRel ctx sf tf` is the hypothesis the simulation carries for first-order calls: every source
callee recorded in `LEnv.funcs` under a `ctx.localCallees` entry `fn ↦ sym` has an LNIR counterpart
`tf sym` that refines it on successful runs, and `sym` is not a runtime intrinsic of `evalExpr`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- `g` refines `f`: every successful run of `f` is a run of `g` with the same result. -/
def FnRefines (f g : FnSem) : Prop := ∀ args hst r, f args hst = .ok r → g args hst = .ok r

/-- The LNIR call table `tf` refines the source call table `sf` at every local callee of `ctx`. -/
def FuncsRel (ctx : RealBridgeCtx) (sf : Lean.Name → Option FnSem) (tf : FuncTable) : Prop :=
  ∀ fn sym f, ctx.findLocalCallee? fn = some sym → sf fn = some f →
    sym ∉ builtinCallNames ∧ ∃ g, tf sym = some g ∧ FnRefines f g

theorem funcsRel_empty (ctx : RealBridgeCtx) (tf : FuncTable) : FuncsRel ctx (fun _ => none) tf :=
  fun _ _ _ _ h => nomatch h

/-- A successful run under the empty table is a run under any table: the table is consulted only
    where `evalExpr` would otherwise fail with `unsupportedCall`. -/
theorem evalExpr_ok_funcs {env : VarEnv} {st : HeapState} {e : LNIRExpr} {r : Val × HeapState}
    (funcs : FuncTable) (h : evalExpr env st e = .ok r) : evalExpr env st e funcs = .ok r := by
  cases e with
  | call fn args rt ext =>
    revert h; dsimp only [evalExpr]
    cases evalVarList env args with
    | error _ => exact id
    | ok vals =>
      dsimp only; intro h
      repeat' (first | exact h | (split <;> rename_i hc <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, reduceCtorEq] at h ⊢))
  | _ => exact h

/-- A non-intrinsic, non-extern call runs its table entry on the argument values. -/
theorem evalExpr_call_table {env : VarEnv} {st : HeapState} {sym : String} {args : List VarId}
    {ty : LNIRType} {funcs : FuncTable} {g : FnSem} {vals : List Val}
    (hb : sym ∉ builtinCallNames) (hg : funcs sym = some g) (hv : evalVarList env args = .ok vals) :
    evalExpr env st (.call sym args ty false) funcs = g vals st := by
  simp only [builtinCallNames, List.mem_cons, List.not_mem_nil, not_or] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hb
  simp [evalExpr, hv, hg, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem bindJpParams_funcs (ctx : RealBridgeCtx) (tys : Lean.FVarId → Option LNIRType) :
    ∀ (env env' : LEnv) ps as_ vs, bindJpParams ctx tys env ps as_ vs = .ok env' → env'.funcs = env.funcs
  | _, _, [], [], [], h => by injection h with h; rw [h]
  | _, env', _ :: ps, _ :: as_, _ :: vs, h => by
    dsimp only [bindJpParams] at h; have h' := bindJpParams_funcs ctx tys _ env' ps as_ vs h; exact h'
  | _, _, [], [], _ :: _, h | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h
  | _, _, _ :: _, _ :: _, [], h => nomatch h

theorem bindParams_funcs (ctx : RealBridgeCtx) (top : Bool) :
    ∀ (env env' : LEnv) ps vs, bindParams ctx top env ps vs = .ok env' → env'.funcs = env.funcs
  | _, _, [], [], h => by injection h with h; rw [h]
  | _, env', _ :: ps, _ :: vs, h => by
    dsimp only [bindParams] at h; have h' := bindParams_funcs ctx top _ env' ps vs h; exact h'
  | _, _, [], _ :: _, h | _, _, _ :: _, [], h => nomatch h

/-- The case-split environment of a `cases` alternative keeps the call table. -/
theorem funcsRel_envIn {ctx : RealBridgeCtx} {lenv : LEnv} {tf : FuncTable}
    (discr? : Option Lean.FVarId) (cname : Lean.Name) (hrel : FuncsRel ctx lenv.funcs tf) :
    FuncsRel ctx (match discr? with
      | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx cname else lenv
      | none => lenv).funcs tf := by
  cases discr? with
  | none => exact hrel
  | some dx => dsimp only; split <;> exact hrel

/-- Induction hypothesis of the step simulation at `fuel`, under call tables related by `FuncsRel`. -/
def StepSimIH (fuel : Nat) (ctx : RealBridgeCtx) (tf : FuncTable) : Prop :=
  ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode),
    BridgeStateInv st lenv venv →
    lowerImpureStepPure fuel ctx st target = .ok (code, st') →
    (match target with
     | .inl c => evalStep fuel ctx lenv hst (.inl c) = .ok (v, hst')
     | .inr (condVar, isBool, idx, discr?, alts) =>
       condVar < st.nextVarId ∧
       (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
       (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
       ∃ cond, venv condVar = some cond ∧
         evalStep fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
    FuncsRel ctx lenv.funcs tf →
    evalCode fuel venv hst code tf = .ok (v, hst')

end LeanNative.Proofs
