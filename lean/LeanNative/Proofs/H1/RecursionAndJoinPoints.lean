import LeanNative.Proofs.H1.FirstOrderCalls

/-!
# W2-L3: fuel-indexed recursion and join points (`RecursionAndJoinPoints.lean`)

W2-L2 call tables are acyclic: an entry sees only the entries after it. A self- or mutually recursive
module is given a table indexed by call depth instead: `RealLCNFSemantics.recModuleFuncEnv` and
`Semantics.recFuncTable` run every entry at depth `depth + 1` under the whole module's depth-`depth`
table, and have no entries at depth `0`. Both evaluators stay structural; a run that needs more nested
calls than `depth` fails, and the statement is about successful runs.

`RecRefinement lowerMod` is the recursive call statement: on an accepted module, the `LNIR` table
refines the source table at every depth. `recRefinement` discharges it for `lowerRealLCNFModule`
(`FuncsRel` is closed under the module at each depth); `lowerRealLCNFRecModule_sound` is the caller-side
corollary.

Join points with parameters (`Code.jp` / `Code.jmp`) are lowered by `lowerImpureStepPure` by inlining
the join-point body at each jump after copying the arguments into fresh `LNIR` variables; that case
is already covered by `specLocked`.

Witnesses (`0 sorryAx`, `0 native_decide`, no new axioms; concrete runs closed by `rfl`):
* `posWitnessSelfRec`: `w3_sumDown 4 = 4 + 3 + 2 + 1 = 10`;
* `posWitnessMutualRec`: `w3_isEven 4 = 1` through `w3_isOdd`;
* `posWitnessJoinPoint`: `w3_jp false 5 = 8` through a parameterized join point.
Mutants: `negWitnessBrokenRecStep`, `negWitnessSwappedMutualTargets` (against `RecRefinement`) and
`negWitnessWrongJoinArg` (against `H1ForwardSim`).
-/

namespace LeanNative.Proofs.H1

open Lean Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics
open LeanNative.Proofs (FuncsRel FnRefines funcsRel_empty lowerRealLCNFDecl_sound_with)

/-- Fuel-indexed recursive call refinement: on an accepted module, the depth-indexed `LNIR` call table
    refines the depth-indexed source table at every depth. -/
def RecRefinement (lowerMod : ModuleLowerer) : Prop :=
  ∀ (fuel : Nat) (ctx : RealBridgeCtx) (entries : List (Decl .impure × String)) (ds : List LNIRDecl),
    ModuleCallees ctx entries → lowerMod fuel ctx entries = .ok ds → ∀ depth,
    FuncsRel ctx (recModuleFuncEnv fuel ctx (entries.map Prod.fst) depth) (recFuncTable fuel ds depth)

/-- One lowered entry, run under related inner tables, extends related tables of the other entries. -/
theorem funcsRel_cons_with (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure) (sym : String)
    (d : LNIRDecl) (sf rf : Name → Option FnSem) (tf rt : FuncTable)
    (hwf : sym ∉ builtinCallNames ∧ ∀ fn, ctx.findLocalCallee? fn = some sym ↔ fn = decl.name)
    (hd : lowerRealLCNFDecl fuel ctx decl sym = .ok d) (hin : FuncsRel ctx sf tf) (hrest : FuncsRel ctx rf rt) :
    FuncsRel ctx (fun n => if n == decl.name then some (fun args st => evalRealLCNFDecl fuel ctx decl args st sf)
        else rf n)
      (fun s => if s == d.name then some (evalDeclWith fuel tf d) else rt s) := by
  intro fn s f hloc hf
  have hname := lowerRealLCNFDecl_name hd
  by_cases hfn : fn = decl.name
  · subst hfn
    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hf
    have hs : some s = some sym := hloc.symm.trans ((hwf.2 decl.name).2 rfl)
    injection hs with hs; subst hs; subst hf
    exact ⟨hwf.1, _, by simp [hname], fun args hst r h =>
      lowerRealLCNFDecl_sound_with fuel ctx decl args hst r.2 r.1 d s sf tf hin hd h⟩
  · simp only [beq_iff_eq, hfn, ↓reduceIte] at hf
    rcases hrest fn s f hloc hf with ⟨hb, g, hg, hfg⟩
    have hs : s ≠ d.name := by rw [hname]; intro hs; subst hs; exact hfn ((hwf.2 fn).1 hloc)
    exact ⟨hb, g, by simp [hs, hg], hfg⟩

/-- A lowered module, every entry run under related inner tables, gives related call tables. -/
theorem funcsRel_with (fuel : Nat) (ctx : RealBridgeCtx) (sf : Name → Option FnSem) (tf : FuncTable)
    (hin : FuncsRel ctx sf tf) :
    ∀ (entries : List (Decl .impure × String)) (ds : List LNIRDecl),
      ModuleCallees ctx entries → lowerRealLCNFModule fuel ctx entries = .ok ds →
      FuncsRel ctx (moduleFuncEnvWith fuel ctx sf (entries.map Prod.fst)) (moduleFuncTableWith fuel tf ds)
  | [], _, _, h => by cases h; exact funcsRel_empty ctx _
  | (decl, sym) :: rest, _, hwf, h => by
    rcases lowerRealLCNFModule_cons h with ⟨d, ds', hd, hrest, rfl⟩
    exact funcsRel_cons_with fuel ctx decl sym d sf _ tf _ (hwf _ (.head _)) hd hin
      (funcsRel_with fuel ctx sf tf hin rest ds' (fun e he => hwf e (.tail _ he)) hrest)

/-- W2-L3 module theorem: at every call depth, the recursive call tables of a lowered module are related. -/
theorem lowerRealLCNFModule_recRel (fuel : Nat) (ctx : RealBridgeCtx) (entries : List (Decl .impure × String))
    (ds : List LNIRDecl) (hwf : ModuleCallees ctx entries) (h : lowerRealLCNFModule fuel ctx entries = .ok ds) :
    ∀ depth, FuncsRel ctx (recModuleFuncEnv fuel ctx (entries.map Prod.fst) depth) (recFuncTable fuel ds depth)
  | 0 => funcsRel_empty ctx _
  | depth + 1 => funcsRel_with fuel ctx _ _ (lowerRealLCNFModule_recRel fuel ctx entries ds hwf h depth)
      entries ds hwf h

theorem recRefinement : RecRefinement lowerRealLCNFModule := lowerRealLCNFModule_recRel

/-- Caller side: a declaration run under a lowered recursive module's depth-`depth` source table runs,
    under the module's depth-`depth` `LNIR` table, to the same result. -/
theorem lowerRealLCNFRecModule_sound (fuel : Nat) (ctx : RealBridgeCtx) (entries : List (Decl .impure × String))
    (ds : List LNIRDecl) (depth : Nat) (decl : Decl .impure) (mangled : String) (d : LNIRDecl)
    (args : List Val) (hst hst' : HeapState) (v : Val) (hwf : ModuleCallees ctx entries)
    (hmod : lowerRealLCNFModule fuel ctx entries = .ok ds) (hd : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst (recModuleFuncEnv fuel ctx (entries.map Prod.fst) depth) =
      .ok (v, hst')) :
    evalDeclWith fuel (recFuncTable fuel ds depth) d args hst = .ok (v, hst') :=
  lowerRealLCNFDecl_sound_with fuel ctx decl args hst hst' v d mangled _ _
    (lowerRealLCNFModule_recRel fuel ctx entries ds hwf hmod depth) hd h_eval

/-! ## Witness module: `w3_sumDown`, `w3_isEven`, `w3_isOdd` -/

def letT (n : Nat) (ty : Expr) (value : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ty, value }

/-- `let z := 0; let c : Bool := x == z; k`. -/
def isZero (k : Code .impure) : Code .impure :=
  .let (letD 2 (.lit (.uint64 0)))
    (.let (letT 3 (mkConst ``Bool) (.fap ``UInt64.decEq #[.fvar (fv 1), .fvar (fv 2)] rfl)) k)

/-- `w3_sumDown n := if n == 0 then 0 else n + w3_sumDown (n - 1)`. -/
def sumDownDecl : Decl .impure := u64Decl `w3_sumDown 1 <| isZero <|
  .cases (Cases.mk ``Bool ImpureType.uint64 (fv 3) #[
    boolAlt 0 (.let (letD 4 (.lit (.uint64 1))) (.let (letD 5 (.fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 4)] rfl))
      (.let (letD 6 (.fap `w3_sumDown #[.fvar (fv 5)] rfl))
      (.let (letD 7 (.fap ``UInt64.add #[.fvar (fv 1), .fvar (fv 6)] rfl)) (.return (fv 7)))))),
    boolAlt 1 (.return (fv 2))])

/-- `name n := if n == 0 then base else other (n - 1)`. -/
def parityDecl (name other : Name) (base : UInt64) : Decl .impure := u64Decl name 1 <| isZero <|
  .cases (Cases.mk ``Bool ImpureType.uint64 (fv 3) #[
    boolAlt 0 (.let (letD 4 (.lit (.uint64 1))) (.let (letD 5 (.fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 4)] rfl))
      (.let (letD 6 (.fap other #[.fvar (fv 5)] rfl)) (.return (fv 6))))),
    boolAlt 1 (.let (letD 4 (.lit (.uint64 base))) (.return (fv 4)))])

def isEvenDecl : Decl .impure := parityDecl `w3_isEven `w3_isOdd 1

def isOddDecl : Decl .impure := parityDecl `w3_isOdd `w3_isEven 0

def w3Module : List (Decl .impure × String) :=
  [(sumDownDecl, "w3_sumDown"), (isEvenDecl, "w3_isEven"), (isOddDecl, "w3_isOdd")]

def w3Ctx : RealBridgeCtx :=
  { paramTypeMap := [(fv 1, .i64)], localCallees := w3Module.map fun (d, s) => (d.name, s) }

def w3Fuel : Nat := 16

/-- Call depth of the witness runs: each needs at most four nested calls. -/
def w3Depth : Nat := 5

theorem w3Ctx_callee (fn : Name) (s : String) :
    w3Ctx.findLocalCallee? fn = some s ↔
      (fn, s) ∈ [(`w3_sumDown, "w3_sumDown"), (`w3_isEven, "w3_isEven"), (`w3_isOdd, "w3_isOdd")] := by
  by_cases h1 : `w3_sumDown = fn
  · subst h1; rw [show w3Ctx.findLocalCallee? `w3_sumDown = some "w3_sumDown" from rfl]; simp [eq_comm]
  by_cases h2 : `w3_isEven = fn
  · subst h2; rw [show w3Ctx.findLocalCallee? `w3_isEven = some "w3_isEven" from rfl]; simp [eq_comm]
  by_cases h3 : `w3_isOdd = fn
  · subst h3; rw [show w3Ctx.findLocalCallee? `w3_isOdd = some "w3_isOdd" from rfl]; simp [eq_comm]
  simp only [RealBridgeCtx.findLocalCallee?, w3Ctx, w3Module, List.map, sumDownDecl, isEvenDecl, isOddDecl,
    parityDecl, u64Decl, List.find?, beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem w3Module_callees : ModuleCallees w3Ctx w3Module := by
  intro e he
  simp only [w3Module, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;>
    exact ⟨by decide, fun fn => by
      rw [w3Ctx_callee]; simp [sumDownDecl, isEvenDecl, isOddDecl, parityDecl, u64Decl]⟩

/-- The recursive `let r := w3_sumDown (n - 1)` lowers to an `LNIR` `.call "w3_sumDown"`. -/
theorem sumDown_lowered_body :
    (lowerRealLCNFDecl w3Fuel w3Ctx sumDownDecl "w3_sumDown").map LNIRDecl.body =
      .ok (.letBind 1 .i64 (.scalar (.constU64 0))
        (.letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.var 1))) (.ite 2 (.ret 1)
          (.letBind 3 .i64 (.scalar (.constU64 1)) (.letBind 4 .i64 (.scalar (.binOp .sub (.var 0) (.var 3)))
            (.letBind 5 .i64 (.call "w3_sumDown" [4] .i64 false)
              (.letBind 6 .i64 (.scalar (.binOp .add (.var 0) (.var 5))) (.ret 6)))))))) := rfl

theorem sumDown_src :
    evalRealLCNFDecl w3Fuel w3Ctx sumDownDecl [.u64 4] .empty
      (recModuleFuncEnv w3Fuel w3Ctx (w3Module.map Prod.fst) (w3Depth - 1)) = .ok (.u64 10, .empty) := rfl

theorem sumDown_tgt : ∀ ds, lowerRealLCNFModule w3Fuel w3Ctx w3Module = .ok ds →
    (recFuncTable w3Fuel ds w3Depth "w3_sumDown").map (fun g => g [.u64 4] .empty) =
      some (.ok (.u64 10, .empty)) :=
  fun _ h => by cases h; rfl

/-- Non-vacuity (self-recursion): the module lowers, `w3_sumDown 4` evaluates to `10` in the source at
    depth `w3Depth`, and `recRefinement` gives the lowered `w3_sumDown` the same result. -/
theorem posWitnessSelfRec :
    ∃ ds g, lowerRealLCNFModule w3Fuel w3Ctx w3Module = .ok ds ∧ recFuncTable w3Fuel ds w3Depth "w3_sumDown" = some g ∧
      evalRealLCNFDecl w3Fuel w3Ctx sumDownDecl [.u64 4] .empty
        (recModuleFuncEnv w3Fuel w3Ctx (w3Module.map Prod.fst) (w3Depth - 1)) = .ok (.u64 10, .empty) ∧
      g [.u64 4] .empty = .ok (.u64 10, .empty) := by
  obtain ⟨ds, hds⟩ : ∃ ds, lowerRealLCNFModule w3Fuel w3Ctx w3Module = .ok ds := ⟨_, rfl⟩
  obtain ⟨-, g, hg, hfg⟩ :=
    recRefinement _ _ _ ds w3Module_callees hds w3Depth `w3_sumDown "w3_sumDown" _ rfl rfl
  exact ⟨ds, g, hds, hg, sumDown_src, hfg _ _ _ sumDown_src⟩

theorem isEven_src :
    evalRealLCNFDecl w3Fuel w3Ctx isEvenDecl [.u64 4] .empty
      (recModuleFuncEnv w3Fuel w3Ctx (w3Module.map Prod.fst) w3Depth) = .ok (.u64 1, .empty) := rfl

theorem isEven_tgt : ∀ ds d, lowerRealLCNFModule w3Fuel w3Ctx w3Module = .ok ds →
    lowerRealLCNFDecl w3Fuel w3Ctx isEvenDecl "w3_isEven" = .ok d →
    evalDeclWith w3Fuel (recFuncTable w3Fuel ds w3Depth) d [.u64 4] .empty = .ok (.u64 1, .empty) :=
  fun _ _ h hd => by cases h; cases hd; rfl

/-- Non-vacuity (mutual recursion): `w3_isEven 4` runs through `w3_isOdd 3`, `w3_isEven 2`, `w3_isOdd 1`,
    `w3_isEven 0` to `1` in the source, and `lowerRealLCNFRecModule_sound` gives the lowered
    `w3_isEven` the same result under the lowered module's table. -/
theorem posWitnessMutualRec :
    ∃ ds d, lowerRealLCNFModule w3Fuel w3Ctx w3Module = .ok ds ∧
      lowerRealLCNFDecl w3Fuel w3Ctx isEvenDecl "w3_isEven" = .ok d ∧
      evalRealLCNFDecl w3Fuel w3Ctx isEvenDecl [.u64 4] .empty
        (recModuleFuncEnv w3Fuel w3Ctx (w3Module.map Prod.fst) w3Depth) = .ok (.u64 1, .empty) ∧
      evalDeclWith w3Fuel (recFuncTable w3Fuel ds w3Depth) d [.u64 4] .empty = .ok (.u64 1, .empty) :=
  ⟨_, _, rfl, rfl, isEven_src,
    lowerRealLCNFRecModule_sound _ _ _ _ _ _ _ _ _ _ _ _ w3Module_callees rfl rfl isEven_src⟩

/-! ## Witness declaration: `w3_jp (b : Bool) (x : UInt64)` with a parameterized join point

```
jp k (y : UInt64) := y + x
cases b | false => let a := 3; jmp k a | true => jmp k x
```
-/

def jpDecl : Decl .impure :=
  { name := `w3_jp, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := #[mkParam 1 (mkConst ``Bool), mkParam 2 ImpureType.uint64]
    value := .code <| .jp ⟨fv 10, `k, #[mkParam 11 ImpureType.uint64], ImpureType.uint64,
        .let (letD 12 (.fap ``UInt64.add #[.fvar (fv 11), .fvar (fv 2)] rfl)) (.return (fv 12))⟩ <|
      .cases (Cases.mk ``Bool ImpureType.uint64 (fv 1) #[
        boolAlt 0 (.let (letD 3 (.lit (.uint64 3))) (.jmp (fv 10) #[.fvar (fv 3)])),
        boolAlt 1 (.jmp (fv 10) #[.fvar (fv 2)])]) }

def jpCtx : RealBridgeCtx := { paramTypeMap := [(fv 1, .i1), (fv 2, .i64)] }

def jpFuel : Nat := 16

def jpArgs (b : Bool) : List Val := [.bool b, .u64 5]

/-- Each `jmp k a` lowers to a copy of `a` into a fresh variable for `y`, followed by the join-point body. -/
theorem jp_lowered_body :
    (lowerRealLCNFDecl jpFuel jpCtx jpDecl "w3_jp").map LNIRDecl.body =
      .ok (.ite 0
        (.letBind 5 .i64 (.scalar (.var 1)) (.letBind 6 .i64 (.scalar (.binOp .add (.var 5) (.var 1))) (.ret 6)))
        (.letBind 2 .i64 (.scalar (.constU64 3)) (.letBind 3 .i64 (.scalar (.var 2))
          (.letBind 4 .i64 (.scalar (.binOp .add (.var 3) (.var 1))) (.ret 4))))) := rfl

theorem jp_src (b : Bool) :
    evalRealLCNFDecl jpFuel jpCtx jpDecl (jpArgs b) .empty = .ok (.u64 (if b then 10 else 8), .empty) := by
  cases b <;> rfl

/-- Non-vacuity (join point): the real lowerer accepts `jpDecl`, the source jumps with `a = 3`, and the
    locked conclusion is `3 + 5 = 8`. -/
theorem posWitnessJoinPoint :
    ∃ d, lowerRealLCNFDecl jpFuel jpCtx jpDecl "w3_jp" = .ok d ∧
      evalRealLCNFDecl jpFuel jpCtx jpDecl (jpArgs false) .empty = .ok (.u64 8, .empty) ∧
      evalLNIRDecl jpFuel d (jpArgs false) .empty = .ok (.u64 8, .empty) :=
  ⟨_, rfl, jp_src false, specLocked _ _ _ _ _ _ _ _ _ rfl (jp_src false)⟩

/-! ## Mutants -/

/-- A module mutant is killed when, on an accepted module, the mutated callee under `sym` at some depth
    disagrees with a successful source run of the callee `fn` at that depth. -/
theorem rec_killed_of_run {f : LNIRDecl → LNIRDecl} {fuel : Nat} {ctx : RealBridgeCtx}
    {entries : List (Decl .impure × String)} (hwf : ModuleCallees ctx entries)
    (hok : ∃ ds, mutateModule f fuel ctx entries = .ok ds) (depth : Nat) (fn : Name) (sym : String)
    (src : FnSem) (args : List Val) (r : Val × HeapState) (r' : Except UBError (Val × HeapState))
    (hsrc : recModuleFuncEnv fuel ctx (entries.map Prod.fst) depth fn = some src)
    (hloc : ctx.findLocalCallee? fn = some sym) (hsrcRun : src args .empty = .ok r)
    (hrun : ∀ ds g, mutateModule f fuel ctx entries = .ok ds → recFuncTable fuel ds depth sym = some g →
      g args .empty = r')
    (hne : r' ≠ .ok r) : ¬ RecRefinement (mutateModule f) := fun h => by
  obtain ⟨ds, hds⟩ := hok
  obtain ⟨-, g, hg, hfg⟩ := h _ _ _ ds hwf hds depth fn sym src hloc hsrc
  exact hne ((hrun ds g hds hg).symm.trans (hfg _ _ _ hsrcRun))

/-- Mutant 1 (broken recursive step): every call passes the variable before each argument, so
    `w3_sumDown` recurses on the constant `1` instead of `n - 1` and never reaches its base case. -/
def negWitnessBrokenRecStep : LNIRDecl → LNIRDecl := fun d =>
  { d with body := mapCalls (fun s args => (s, args.map (· - 1))) d.body }

/-- Mutant 2 (swapped mutual targets): `w3_isEven` and `w3_isOdd` call themselves instead of each other. -/
def negWitnessSwappedMutualTargets : LNIRDecl → LNIRDecl := fun d =>
  { d with body := mapCalls (fun s args =>
      (if s == "w3_isOdd" then "w3_isEven" else if s == "w3_isEven" then "w3_isOdd" else s, args)) d.body }

/-- The broken `w3_sumDown 4` exhausts the call depth where the source returns `10`. -/
theorem negWitnessBrokenRecStep_killed : ¬ RecRefinement (mutateModule negWitnessBrokenRecStep) :=
  rec_killed_of_run (fuel := w3Fuel) w3Module_callees ⟨_, rfl⟩ w3Depth `w3_sumDown "w3_sumDown" _ [.u64 4] (.u64 10, .empty)
    (.error (.unsupportedCall "w3_sumDown")) rfl rfl sumDown_src
    (fun _ _ hds hg => by cases hds; injection hg with hg; subst hg; rfl) (by simp)

/-- The swapped `w3_isEven 3` counts down through itself to `1` where the source returns `0`. -/
theorem negWitnessSwappedMutualTargets_killed : ¬ RecRefinement (mutateModule negWitnessSwappedMutualTargets) :=
  rec_killed_of_run (fuel := w3Fuel) w3Module_callees ⟨_, rfl⟩ w3Depth `w3_isEven "w3_isEven" _ [.u64 3] (.u64 0, .empty)
    (.ok (.u64 1, .empty)) rfl rfl rfl
    (fun _ _ hds hg => by cases hds; injection hg with hg; subst hg; rfl) (by simp)

/-- Rewrite every variable copy `x := y`, the form a lowered join-point argument takes. -/
def mapVarCopies (f : VarId → VarId) : LNIRCode → LNIRCode
  | .letBind x ty (.scalar (.var y)) k => .letBind x ty (.scalar (.var (f y))) (mapVarCopies f k)
  | .letBind x ty e k => .letBind x ty e (mapVarCopies f k)
  | .rawStore p i v ty k => .rawStore p i v ty (mapVarCopies f k)
  | .incRef x n k => .incRef x n (mapVarCopies f k)
  | .decRef x n k => .decRef x n (mapVarCopies f k)
  | .ite c t e => .ite c (mapVarCopies f t) (mapVarCopies f e)
  | .seqFor i lo hi a ai ty s k => .seqFor i lo hi a ai ty (mapVarCopies f s) (mapVarCopies f k)
  | .parFor o n xs ty kk k => .parFor o n xs ty kk (mapVarCopies f k)
  | c => c

/-- Mutant 3 (wrong join argument): each jump passes the variable before its argument. -/
def negWitnessWrongJoinArg : LNIRDecl → LNIRDecl := fun d => { d with body := mapVarCopies (· - 1) d.body }

/-- The mutated `jmp k a` passes `x = 5` and computes `5 + 5` where the source computes `3 + 5 = 8`. -/
theorem negWitnessWrongJoinArg_killed : ¬ H1ForwardSim (mutate negWitnessWrongJoinArg) := fun h =>
  absurd ((show ∀ d, lowerRealLCNFDecl jpFuel jpCtx jpDecl "w3_jp" = .ok d →
      evalLNIRDecl jpFuel (negWitnessWrongJoinArg d) (jpArgs false) .empty = .ok (.u64 10, .empty)
    from fun _ hd => by cases hd; rfl) _ rfl |>.symm.trans (h _ _ _ _ _ _ _ _ _ rfl (jp_src false))) (by simp)

end LeanNative.Proofs.H1
