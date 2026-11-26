import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval

/-!
# Fuel-Indexed Recursion-Capable LNIR Evaluator (`evalCodeR`) — rung L3

The L3 extension of `evalCode` with a function environment whose calls are FUEL-INDEXED
(L3 contract, `Proofs/LowerRec.lean`): a `Φ`-bound `.call` consumes one unit of fuel and
the callee re-runs under the WHOLE environment, so self and mutual recursion evaluate,
bounded by call depth. `Φ = []` is the old evaluator by theorem (`evalCodeR_nil`,
`Proofs/LowerRec.lean`). This file is NEW rather than an append to `Semantics/Eval.lean`,
which stays append-only for the L2 lane; `List LNIRDecl` is spelled out rather than L2's
`FuncEnv` abbrev so the two lanes cannot collide (the spellings are one type).

`evalCodeR` is layered for structural termination: `evalCodeRAux` mirrors `evalCode`
clause for clause by structural recursion on the code, taking the one-level-down callee
evaluator as a parameter (`none` = the budget is spent), and `evalCodeR` ties the levels
by structural recursion on the fuel. The layering is definitionally the lexicographic
`(fuel, code)` recursion the contract describes, with pristine equation lemmas.
-/

namespace LeanNative.Semantics

open LeanNative.IR

/-- First declaration named `fn`. The hit alone — the callee re-runs under the SAME
    full environment, which is what admits self and mutual recursion (L3 contract;
    compare L2's strict-suffix `FuncEnv.lookup?`, which stratifies calls instead). -/
def lookupFuncRec? : List LNIRDecl → String → Option LNIRDecl
  | [], _ => none
  | ld :: Φ, fn => if ld.name == fn then some ld else lookupFuncRec? Φ fn

/-- A `lookupFuncRec?` hit is a member with that name (the alignment half the
    `DeclEnvLowersR` freshness clause consumes). -/
theorem lookupFuncRec?_mem : ∀ (Φ : List LNIRDecl) (fn : String) (ld : LNIRDecl),
    lookupFuncRec? Φ fn = some ld → ld ∈ Φ ∧ ld.name = fn
  | [], _, _, h => nomatch h
  | ld0 :: Φ, fn, ld, h => by
    dsimp only [lookupFuncRec?] at h
    split at h
    · next hb =>
      injection h with h'
      subst h'
      exact ⟨List.mem_cons_self .., eq_of_beq hb⟩
    · next =>
      have ⟨hm, hn⟩ := lookupFuncRec?_mem Φ fn ld h
      exact ⟨List.mem_cons_of_mem _ hm, hn⟩

/-- One level of the fuel-indexed evaluator: mirrors `evalCode` clause for clause
    (same `evalExpr`, same `evalSeqLoop`/`evalParFor` helpers, `budget` carried only as
    `evalParFor`'s evaluator budget, exactly where `evalCode` passes its `fuel`), with
    ONE new rule: a non-extern `.call` whose name `lookupFuncRec? Φ` resolves runs — if
    the level below exists (`callee? = some`) and the argument count matches the callee's
    parameters (else `.typeError "call arity mismatch"`, as L2's `evalCodeF`) — the callee
    body under `callee?` with the
    declaration-entry binding convention, then the continuation at THIS level. At the
    spent level (`callee? = none`) a resolved call is `.error .fuelExhausted` BEFORE its
    arguments are read: an evaluator budget, never source UB. An extern call, a lookup
    miss, and every non-call binding delegate to `evalExpr` exactly as `evalCode` does. -/
def evalCodeRAux (Φ : List LNIRDecl) (budget : Nat)
    (callee? : Option (VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState))) :
    VarEnv → HeapState → LNIRCode → Except UBError (Val × HeapState)
  | env, st, .letBind dst _ty val k =>
    match val with
    | .call fn args retTy false =>
      match lookupFuncRec? Φ fn with
      | some ld =>
        match callee? with
        | none => .error .fuelExhausted
        | some callee =>
          match evalVarList env args with
          | .ok vals =>
            -- Strict arity, as L2's `evalCodeF` (review F4 of both lanes): the source
            -- side's `bindParams` refuses a count mismatch, so this side does too.
            if vals.length = ld.params.length then
              match callee
                  ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
                  st ld.body with
              | .ok (v, st') => evalCodeRAux Φ budget callee? (env.bind dst v) st' k
              | .error err => .error err
            else .error (.typeError "call arity mismatch")
          | .error err => .error err
      | none =>
        match evalExpr env st (.call fn args retTy false) with
        | .ok (v, st') => evalCodeRAux Φ budget callee? (env.bind dst v) st' k
        | .error err => .error err
    | _ =>
      match evalExpr env st val with
      | .ok (v, st') => evalCodeRAux Φ budget callee? (env.bind dst v) st' k
      | .error err => .error err
  | env, st, .rawStore ptrVar idxVar valVar elemTy k =>
    match env ptrVar, env idxVar, env valVar with
    | some (.rawPtrId bufId), some (.u64 idx), some (.u64 val) =>
      match st.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) with
      | .ok st' => evalCodeRAux Φ budget callee? env st' k
      | .error err => .error err
    | some (.sarrayId bufId), some (.u64 idx), some (.u64 val) =>
      match st.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) with
      | .ok st' => evalCodeRAux Φ budget callee? env st' k
      | .error err => .error err
    | none, _, _ => .error (.unboundVar ptrVar)
    | _, none, _ => .error (.unboundVar idxVar)
    | _, _, none => .error (.unboundVar valVar)
    | _, _, _ => .error (.typeError "rawStore requires rawPtrId/sarrayId and u64 index/value")
  | env, st, .incRef objVar count k =>
    match st.evalIncRef env objVar count with
    | .ok st' => evalCodeRAux Φ budget callee? env st' k
    | .error err => .error err
  | env, st, .decRef objVar count k =>
    match st.evalDecRef env objVar count with
    | .ok st' => evalCodeRAux Φ budget callee? env st' k
    | .error err => .error err
  | env, st, .ite condVar thenBranch elseBranch =>
    match env condVar with
    | some (.bool true) => evalCodeRAux Φ budget callee? env st thenBranch
    | some (.bool false) => evalCodeRAux Φ budget callee? env st elseBranch
    | some (.u64 n) =>
      if n != 0 then evalCodeRAux Φ budget callee? env st thenBranch
      else evalCodeRAux Φ budget callee? env st elseBranch
    | some (.u256 w) =>
      if w != UInt256.zero then evalCodeRAux Φ budget callee? env st thenBranch
      else evalCodeRAux Φ budget callee? env st elseBranch
    | some _ => .error (.typeError "ite condition must be bool, u64, or u64")
    | none => .error (.unboundVar condVar)
  | env, st, .seqFor idxVar loVar hiVar accVar accInit _accTy stepBody k =>
    match env loVar, env hiVar, env accInit with
    | some (.u64 lo), some (.u64 hi), some initVal =>
      let count := hi.toNat - lo.toNat
      match evalSeqLoop count lo.toNat idxVar accVar initVal env st
          (fun stepEnv stepSt => evalCodeRAux Φ budget callee? stepEnv stepSt stepBody) with
      | .ok (finalAcc, st') => evalCodeRAux Φ budget callee? (env.bind accVar finalAcc) st' k
      | .error err => .error err
    | none, _, _ => .error (.unboundVar loVar)
    | _, none, _ => .error (.unboundVar hiVar)
    | _, _, none => .error (.unboundVar accInit)
    | _, _, _ => .error (.typeError "seqFor bounds must be u64")
  | env, st, .parFor outVar lenVar inputs elemTy kernel k =>
    match evalParFor budget env st lenVar inputs kernel elemTy with
    | .ok (outVal, st') => evalCodeRAux Φ budget callee? (env.bind outVar outVal) st' k
    | .error err => .error err
  | env, st, .ret v =>
    match env v with
    | some val => .ok (val, st)
    | none => .error (.unboundVar v)
  | _, _, .unreachable =>
    .error (.typeError "reached unreachable code")

/-- Fuel-indexed recursion-capable evaluator (L3 contract, `Proofs/LowerRec.lean`):
    `fuel` bounds the DEPTH of `Φ`-call nesting — a resolved call runs its callee one
    level down and its continuation at the same level — so sequential calls at one level
    share a budget and self/mutual recursion terminates by fuel. Every non-call clause
    is `evalCode`'s, so `evalCodeR [] fuel = evalCode fuel` (`evalCodeR_nil`). -/
def evalCodeR (Φ : List LNIRDecl) : Nat → VarEnv → HeapState → LNIRCode →
    Except UBError (Val × HeapState)
  | 0 => evalCodeRAux Φ 0 none
  | fuel + 1 => evalCodeRAux Φ (fuel + 1) (some (evalCodeR Φ fuel))

end LeanNative.Semantics
