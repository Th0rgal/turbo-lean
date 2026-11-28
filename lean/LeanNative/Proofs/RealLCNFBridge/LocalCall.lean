import LeanNative.Proofs.RealLCNFBridge.StepCases

/-!
# W2-L2: a `let` bound to a first-order local call (`LocalCall.lean`)

`lowerImpureStepPure` lowers `let x := fn args` for a `ctx.localCallees` entry `fn ↦ sym` to
`.call sym argVars ty false`, binding every erased argument to a fresh `.unit` variable holding `0`.
`lowerLocalCall_sound` shows the lowered code runs to the source result whenever the source callee
`lenv.funcs fn` succeeds and `FuncsRel` relates it to the LNIR callee `tf sym`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Soundness of `lowerCallArgsWithErasedPure` on `args`: the argument variables evaluate to the
    source arguments once the zero bindings for erased arguments have run. -/
def CallArgsSound (ctx : RealBridgeCtx) (fuel : Nat) (hst : HeapState) (tf : FuncTable)
    (args : List (Lean.Compiler.LCNF.Arg .impure)) : Prop :=
  ∀ (st st1 : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (vids : List VarId)
    (zs : List (VarId × LNIRType)) (vs : List Val),
    BridgeStateInv st lenv venv →
    lowerCallArgsWithErasedPure ctx st args = .ok (vids, zs, st1) →
    evalJpArgs lenv.vals args = .ok vs →
    ∃ venvZ, BridgeStateInv st1 lenv venvZ ∧ (∀ u, u < st.nextVarId → venvZ u = venv u) ∧
      evalVarList venvZ vids = .ok vs ∧
      ∀ body, evalCode fuel venv hst (wrapZeroScalarSlotsPure zs body) tf = evalCode fuel venvZ hst body tf

theorem callArgsSound_nil (ctx : RealBridgeCtx) (fuel : Nat) (hst : HeapState) (tf : FuncTable) :
    CallArgsSound ctx fuel hst tf [] := by
  intro st st1 lenv venv vids zs vs hinv hl he
  injection hl with hp; injection he with hv
  cases hp; cases hv
  exact ⟨venv, hinv, fun _ _ => rfl, rfl, fun _ => rfl⟩

/-- An erased argument: a fresh `.unit` variable bound to `0`, the value `evalJpArg` gives it. -/
theorem callArgsSound_erased (ctx : RealBridgeCtx) (fuel : Nat) (hst : HeapState) (tf : FuncTable)
    (rest : List (Lean.Compiler.LCNF.Arg .impure)) (ih : CallArgsSound ctx fuel hst tf rest) :
    CallArgsSound ctx fuel hst tf (.erased :: rest) := by
  intro st st1 lenv venv vids zs vs hinv hl he
  dsimp only [lowerCallArgsWithErasedPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at hl
  cases hr : lowerCallArgsWithErasedPure ctx (st.freshVar .unit).2 rest with
  | error _ => rw [hr] at hl; exact nomatch hl
  | ok pr =>
    rw [hr] at hl; injection hl with hp; cases hp
    dsimp only [evalJpArgs, evalJpArg] at he
    cases hrest : evalJpArgs lenv.vals rest with
    | error _ => rw [hrest] at he; exact nomatch he
    | ok vsr =>
      rw [hrest] at he; injection he with hv; subst hv
      rcases freshVar_spec st .unit with ⟨hfv1, hfvNext, -⟩
      rcases ih _ pr.2.2 lenv _ pr.1 pr.2.1 vsr (bridgeInv_freshVar st lenv venv .unit (.u64 0) hinv) hr hrest
        with ⟨venvZ, hinvZ, hagree, hvl, hwrap⟩
      have hzLt : (st.freshVar .unit).1 < (st.freshVar .unit).2.nextVarId := by
        rw [hfv1, hfvNext]; exact Nat.lt_succ_self _
      refine ⟨venvZ, hinvZ, fun u hu => ?_, ?_, fun body => ?_⟩
      · rw [hagree u (by rw [hfvNext]; exact Nat.lt_succ_of_lt hu), hfv1]
        exact venv_bind_fresh venv _ u hu _
      · dsimp only [evalVarList]; rw [hagree _ hzLt, VarEnv.bind_self, hvl]
      · dsimp only [wrapZeroScalarSlotsPure, evalCode, evalExpr, evalScalarExpr]; exact hwrap body

/-- A variable argument: `lowerRealArg` returns its SSA variable and leaves the state unchanged. -/
theorem callArgsSound_fvar (ctx : RealBridgeCtx) (fuel : Nat) (hst : HeapState) (tf : FuncTable)
    (x : Lean.FVarId) (rest : List (Lean.Compiler.LCNF.Arg .impure)) (ih : CallArgsSound ctx fuel hst tf rest) :
    CallArgsSound ctx fuel hst tf (.fvar x :: rest) := by
  intro st st1 lenv venv vids zs vs hinv hl he
  dsimp only [lowerCallArgsWithErasedPure, Bind.bind, Except.bind, Pure.pure, Except.pure] at hl
  cases ha : lowerRealArg ctx st (.fvar x) true with
  | error _ => rw [ha] at hl; exact nomatch hl
  | ok pa =>
    rw [ha] at hl; dsimp only at hl
    rcases lowerRealArg_sound ctx st lenv venv (.fvar x) true pa.1 pa.2 hinv ha with
      ⟨x0, val, hx0, hlu, hevA, hvV, _, hstEq⟩
    cases hx0
    rw [hstEq] at hl
    cases hr : lowerCallArgsWithErasedPure ctx st rest with
    | error _ => rw [hr] at hl; exact nomatch hl
    | ok pr =>
      rw [hr] at hl; injection hl with hp; cases hp
      have hj : evalJpArg lenv.vals (.fvar x) = .ok val := hevA
      dsimp only [evalJpArgs] at he; rw [hj] at he
      cases hrest : evalJpArgs lenv.vals rest with
      | error _ => rw [hrest] at he; exact nomatch he
      | ok vsr =>
        rw [hrest] at he; injection he with hv; subst hv
        rcases ih st pr.2.2 lenv venv pr.1 pr.2.1 vsr hinv hr hrest with ⟨venvZ, hinvZ, hagree, hvl, hwrap⟩
        refine ⟨venvZ, hinvZ, hagree, ?_, hwrap⟩
        dsimp only [evalVarList]; rw [hagree _ (hinv.fvar_lt x pa.1 hlu), hvV, hvl]

theorem callArgsSound (ctx : RealBridgeCtx) (fuel : Nat) (hst : HeapState) (tf : FuncTable) :
    ∀ args, CallArgsSound ctx fuel hst tf args
  | [] => callArgsSound_nil ctx fuel hst tf
  | .fvar x :: rest => callArgsSound_fvar ctx fuel hst tf x rest (callArgsSound ctx fuel hst tf rest)
  | .erased :: rest => callArgsSound_erased ctx fuel hst tf rest (callArgsSound ctx fuel hst tf rest)
  | .type _ h :: _ => nomatch h

/-- Source side of a local call: the callee ran on the evaluated arguments, and the continuation runs
    with the result bound at the `let` type. -/
theorem evalLocalCall_inv (fuel : Nat) (ctx : RealBridgeCtx) (lenv : LEnv) (hst hst' : HeapState) (v : Val)
    (fvarId : Lean.FVarId) (binderName : Lean.Name) (declTy : Lean.Expr) (fn : Lean.Name)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (k : Lean.Compiler.LCNF.Code .impure) (sym : String) (hloc : ctx.findLocalCallee? fn = some sym)
    (h_eval : evalStep (fuel + 1) ctx lenv hst
      (.inl (.let ⟨fvarId, binderName, declTy, .fap fn args himp⟩ k)) = .ok (v, hst')) :
    ∃ f vs r hst1, lenv.funcs fn = some f ∧ evalJpArgs lenv.vals args.toList = .ok vs ∧
      f vs hst = .ok (r, hst1) ∧
      evalStep fuel ctx (lenv.bind fvarId r none (some (lowerGroundImpureTypeWith ctx declTy))) hst1
        (.inl k) = .ok (v, hst') := by
  dsimp only [evalStep, evalLetValue] at h_eval
  rw [hloc] at h_eval; simp only [Option.isSome, ↓reduceIte] at h_eval
  cases hf : lenv.funcs fn with
  | none => rw [hf] at h_eval; exact nomatch h_eval
  | some f =>
    rw [hf] at h_eval
    cases hsc : isUnboxedScalarOrTuple (lowerGroundImpureTypeWith ctx declTy) <;>
      simp only [hsc, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h_eval
    · exact nomatch h_eval
    cases hj : evalJpArgs lenv.vals args.toList with
    | error _ => rw [hj] at h_eval; exact nomatch h_eval
    | ok vs =>
      rw [hj] at h_eval; dsimp only at h_eval
      cases hc : f vs hst with
      | error _ => rw [hc] at h_eval; exact nomatch h_eval
      | ok p => rw [hc] at h_eval; dsimp only [Except.map] at h_eval; exact ⟨f, vs, p.1, p.2, rfl, rfl, hc, h_eval⟩

/-- The `.fap` arm of `lowerImpureStepPure` for `let x : declTy := fn args` with `fn ↦ sym` in `ctx.localCallees`. -/
def lowerLocalCallStep (fuel : Nat) (ctx : RealBridgeCtx) (st : RealBridgeState) (fvarId : Lean.FVarId)
    (declTy : Lean.Expr) (args : Array (Lean.Compiler.LCNF.Arg .impure)) (k : Lean.Compiler.LCNF.Code .impure)
    (sym : String) : Except String (LNIRCode × RealBridgeState) := do
  let (argVars, zeroBinds, st1) ← lowerCallArgsWithErasedPure ctx st args.toList
  let (dst, st2) := st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)
  let (kCode, st3) ← lowerImpureStepPure fuel ctx st2 (.inl k)
  return (wrapZeroScalarSlotsPure zeroBinds (.letBind dst (lowerGroundImpureTypeWith ctx declTy)
    (.call sym argVars (lowerGroundImpureTypeWith ctx declTy) false) kCode), st3)

/-- A `let` bound to a local call: the lowered `.call` runs the LNIR callee, which refines the source one. -/
theorem lowerLocalCall_sound {tf : FuncTable} (fuel : Nat) (ctx : RealBridgeCtx) (ih : StepSimIH fuel ctx tf)
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (fvarId : Lean.FVarId) (binderName : Lean.Name) (declTy : Lean.Expr) (fn : Lean.Name)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode) (sym : String) (hinv : BridgeStateInv st lenv venv)
    (hloc : ctx.findLocalCallee? fn = some sym)
    (h_lower : lowerLocalCallStep fuel ctx st fvarId declTy args k sym = .ok (code, st'))
    (h_eval : evalStep (fuel + 1) ctx lenv hst
      (.inl (.let ⟨fvarId, binderName, declTy, .fap fn args himp⟩ k)) = .ok (v, hst'))
    (hrel : FuncsRel ctx lenv.funcs tf) :
    evalCode (fuel + 1) venv hst code tf = .ok (v, hst') := by
  rcases evalLocalCall_inv fuel ctx lenv hst hst' v fvarId binderName declTy fn args himp k sym hloc h_eval
    with ⟨f, vs, r, hst1, hf, hj, hc, hk⟩
  rcases hrel fn sym f hloc hf with ⟨hb, g, hg, hfg⟩
  dsimp only [lowerLocalCallStep, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
  cases ha : lowerCallArgsWithErasedPure ctx st args.toList with
  | error _ => rw [ha] at h_lower; exact nomatch h_lower
  | ok pa =>
    rw [ha] at h_lower; rcases pa with ⟨vids, zs, st1⟩; dsimp only at h_lower
    rcases callArgsSound ctx (fuel + 1) hst tf args.toList st st1 lenv venv vids zs vs hinv ha hj with
      ⟨venvZ, hinvZ, -, hvl, hwrap⟩
    cases hkl : lowerImpureStepPure fuel ctx (st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)).2
        (.inl k) with
    | error _ => rw [hkl] at h_lower; exact nomatch h_lower
    | ok pk =>
      rw [hkl] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
      have hinv2 := bridgeInv_bind_fresh st1 lenv venvZ fvarId (lowerGroundImpureTypeWith ctx declTy) r hinvZ
      have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst1 v hst'
        (ih _ pk.2 _ _ hst1 hst' v (.inl k) pk.1 hinv2 hkl hk hrel)
      rw [hwrap]; dsimp only [evalCode]; rw [evalExpr_call_table hb hg hvl, hfg vs hst (r, hst1) hc]; exact hkEval

end LeanNative.Proofs
