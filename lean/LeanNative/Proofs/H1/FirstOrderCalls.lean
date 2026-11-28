import LeanNative.Proofs.H1.LowerSound

/-!
# W2-L2: first-order calls (`FirstOrderCalls.lean`)

A module is a list of `(Decl .impure, symbol)` entries in which callers precede their callees.
`RealLCNFSemantics.moduleFuncEnv` gives each entry the source semantics of the entries after it, keyed by
`Decl.name`; `Semantics.moduleFuncTable` does the same for the lowered `LNIRDecl`s, keyed by
`LNIRDecl.name` (the mangled symbol). Both are built by structural recursion on the list, so the
evaluators stay structural and a call consumes no fuel of the caller.

`CallRefinement lowerMod` is the first-order call statement: on a module whose symbols are exactly
its `ctx.localCallees` entries, every source callee is refined by the `LNIR` callee under its
symbol. `callRefinement` discharges it for `lowerRealLCNFModule`; `lowerRealLCNFModule_sound` is the
caller-side corollary. `posWitnessCall` (`w2_f x = w2_g x + 1`, `w2_g y = y * 2`) is non-vacuity;
`negWitnessWrongCallTarget` and `negWitnessSwappedCallArgs` are lowerer mutants it rejects.
-/

namespace LeanNative.Proofs.H1

open Lean Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics
open LeanNative.Proofs (FuncsRel FnRefines funcsRel_empty lowerRealLCNFDecl_sound_with)

/-- Signature of a module lowerer: the shape of `lowerRealLCNFModule fuel ctx entries`. -/
abbrev ModuleLowerer := Nat → RealBridgeCtx → List (Decl .impure × String) → Except String (List LNIRDecl)

/-- Each entry's symbol is the `ctx.localCallees` symbol of its own declaration and of no other name,
    and is not a runtime intrinsic of `evalExpr`. -/
def ModuleCallees (ctx : RealBridgeCtx) (entries : List (Decl .impure × String)) : Prop :=
  ∀ e ∈ entries, e.2 ∉ builtinCallNames ∧ ∀ fn, ctx.findLocalCallee? fn = some e.2 ↔ fn = e.1.name

/-- First-order call refinement: on an accepted module, the `LNIR` call table refines the source one. -/
def CallRefinement (lowerMod : ModuleLowerer) : Prop :=
  ∀ (fuel : Nat) (ctx : RealBridgeCtx) (entries : List (Decl .impure × String)) (ds : List LNIRDecl),
    ModuleCallees ctx entries → lowerMod fuel ctx entries = .ok ds →
    FuncsRel ctx (moduleFuncEnv fuel ctx (entries.map Prod.fst)) (moduleFuncTable fuel ds)

theorem lowerRealLCNFDecl_name {fuel : Nat} {ctx : RealBridgeCtx} {decl : Decl .impure} {m : String}
    {d : LNIRDecl} (h : lowerRealLCNFDecl fuel ctx decl m = .ok d) : d.name = m := by
  unfold lowerRealLCNFDecl at h
  cases hdv : decl.value with
  | extern _ => rw [hdv] at h; exact nomatch h
  | code c =>
    rw [hdv] at h; dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hlc : lowerRealLCNFCode fuel ctx (internRealParams ctx {} decl.params.toList).2 c with
    | error _ => rw [hlc] at h; exact nomatch h
    | ok _ => rw [hlc] at h; injection h with hd; rw [← hd]

theorem lowerRealLCNFModule_cons {fuel : Nat} {ctx : RealBridgeCtx} {decl : Decl .impure} {sym : String}
    {rest : List (Decl .impure × String)} {ds : List LNIRDecl}
    (h : lowerRealLCNFModule fuel ctx ((decl, sym) :: rest) = .ok ds) :
    ∃ d ds', lowerRealLCNFDecl fuel ctx decl sym = .ok d ∧ lowerRealLCNFModule fuel ctx rest = .ok ds' ∧
      ds = d :: ds' := by
  dsimp only [lowerRealLCNFModule, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hd : lowerRealLCNFDecl fuel ctx decl sym with
  | error _ => rw [hd] at h; exact nomatch h
  | ok d =>
    rw [hd] at h; dsimp only at h
    cases hr : lowerRealLCNFModule fuel ctx rest with
    | error _ => rw [hr] at h; exact nomatch h
    | ok ds' => rw [hr] at h; injection h with h; exact ⟨d, ds', rfl, rfl, h.symm⟩

/-- Adding one lowered declaration to related call tables keeps them related. -/
theorem funcsRel_cons (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure) (sym : String) (d : LNIRDecl)
    (sf : Name → Option FnSem) (tf : FuncTable)
    (hwf : sym ∉ builtinCallNames ∧ ∀ fn, ctx.findLocalCallee? fn = some sym ↔ fn = decl.name)
    (hd : lowerRealLCNFDecl fuel ctx decl sym = .ok d) (hrel : FuncsRel ctx sf tf) :
    FuncsRel ctx (fun n => if n == decl.name then some (fun args st => evalRealLCNFDecl fuel ctx decl args st sf)
        else sf n)
      (fun s => if s == d.name then some (evalDeclWith fuel tf d) else tf s) := by
  intro fn s f hloc hf
  have hname := lowerRealLCNFDecl_name hd
  by_cases hfn : fn = decl.name
  · subst hfn
    simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hf
    have hs : some s = some sym := hloc.symm.trans ((hwf.2 decl.name).2 rfl)
    injection hs with hs; subst hs; subst hf
    exact ⟨hwf.1, _, by simp [hname], fun args hst r h =>
      lowerRealLCNFDecl_sound_with fuel ctx decl args hst r.2 r.1 d s sf tf hrel hd h⟩
  · simp only [beq_iff_eq, hfn, ↓reduceIte] at hf
    rcases hrel fn s f hloc hf with ⟨hb, g, hg, hfg⟩
    have hs : s ≠ d.name := by rw [hname]; intro hs; subst hs; exact hfn ((hwf.2 fn).1 hloc)
    exact ⟨hb, g, by simp [hs, hg], hfg⟩

/-- W2-L2 module theorem: the call tables of a lowered module are related. -/
theorem lowerRealLCNFModule_rel (fuel : Nat) (ctx : RealBridgeCtx) :
    ∀ (entries : List (Decl .impure × String)) (ds : List LNIRDecl),
      ModuleCallees ctx entries → lowerRealLCNFModule fuel ctx entries = .ok ds →
      FuncsRel ctx (moduleFuncEnv fuel ctx (entries.map Prod.fst)) (moduleFuncTable fuel ds)
  | [], _, _, h => by cases h; exact funcsRel_empty ctx _
  | (decl, sym) :: rest, _, hwf, h => by
    rcases lowerRealLCNFModule_cons h with ⟨d, ds', hd, hrest, rfl⟩
    exact funcsRel_cons fuel ctx decl sym d _ _ (hwf _ (.head _)) hd
      (lowerRealLCNFModule_rel fuel ctx rest ds' (fun e he => hwf e (.tail _ he)) hrest)

theorem callRefinement : CallRefinement lowerRealLCNFModule := lowerRealLCNFModule_rel

/-- Caller side: a declaration calling into a lowered module runs, under the module's `LNIR` call
    table, to its source result under the module's source call table. -/
theorem lowerRealLCNFModule_sound (fuel : Nat) (ctx : RealBridgeCtx) (entries : List (Decl .impure × String))
    (ds : List LNIRDecl) (decl : Decl .impure) (mangled : String) (d : LNIRDecl) (args : List Val)
    (hst hst' : HeapState) (v : Val) (hwf : ModuleCallees ctx entries)
    (hmod : lowerRealLCNFModule fuel ctx entries = .ok ds) (hd : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst (moduleFuncEnv fuel ctx (entries.map Prod.fst)) =
      .ok (v, hst')) :
    evalDeclWith fuel (moduleFuncTable fuel ds) d args hst = .ok (v, hst') :=
  lowerRealLCNFDecl_sound_with fuel ctx decl args hst hst' v d mangled _ _
    (lowerRealLCNFModule_rel fuel ctx entries ds hwf hmod) hd h_eval

/-! ## Witness module -/

def letD (n : Nat) (value : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ImpureType.uint64, value }

def u64Decl (name : Name) (arity : Nat) (body : Code .impure) : Decl .impure :=
  { name, levelParams := [], type := ImpureType.uint64, inlineAttr? := none
    params := ((List.range arity).map fun i => mkParam (i + 1) ImpureType.uint64).toArray
    value := .code body }

/-- `w2_f x := w2_g x + 1`. -/
def fDecl : Decl .impure := u64Decl `w2_f 1
  (.let (letD 2 (.fap `w2_g #[.fvar (fv 1)] rfl)) (.let (letD 3 (.lit (.uint64 1)))
    (.let (letD 4 (.fap ``UInt64.add #[.fvar (fv 2), .fvar (fv 3)] rfl)) (.return (fv 4)))))

/-- `w2_d x y := w2_k x y`. -/
def dDecl : Decl .impure := u64Decl `w2_d 2
  (.let (letD 3 (.fap `w2_k #[.fvar (fv 1), .fvar (fv 2)] rfl)) (.return (fv 3)))

/-- `w2_g y := y * 2`. -/
def gDecl : Decl .impure := u64Decl `w2_g 1
  (.let (letD 2 (.lit (.uint64 2))) (.let (letD 3 (.fap ``UInt64.mul #[.fvar (fv 1), .fvar (fv 2)] rfl))
    (.return (fv 3))))

/-- `w2_h y := y + 3`, the wrong target of `negWitnessWrongCallTarget`. -/
def hDecl : Decl .impure := u64Decl `w2_h 1
  (.let (letD 2 (.lit (.uint64 3))) (.let (letD 3 (.fap ``UInt64.add #[.fvar (fv 1), .fvar (fv 2)] rfl))
    (.return (fv 3))))

/-- `w2_k a b := a - b`. -/
def kDecl : Decl .impure := u64Decl `w2_k 2
  (.let (letD 3 (.fap ``UInt64.sub #[.fvar (fv 1), .fvar (fv 2)] rfl)) (.return (fv 3)))

def w2Module : List (Decl .impure × String) :=
  [(fDecl, "w2_f"), (dDecl, "w2_d"), (gDecl, "w2_g"), (hDecl, "w2_h"), (kDecl, "w2_k")]

def w2Ctx : RealBridgeCtx :=
  { paramTypeMap := [(fv 1, .i64), (fv 2, .i64)]
    localCallees := w2Module.map fun (d, s) => (d.name, s) }

def w2Fuel : Nat := 8

theorem w2Ctx_callee (fn : Name) (s : String) :
    w2Ctx.findLocalCallee? fn = some s ↔
      (fn, s) ∈ [(`w2_f, "w2_f"), (`w2_d, "w2_d"), (`w2_g, "w2_g"), (`w2_h, "w2_h"), (`w2_k, "w2_k")] := by
  by_cases h1 : `w2_f = fn
  · subst h1; rw [show w2Ctx.findLocalCallee? `w2_f = some "w2_f" from rfl]; simp [eq_comm]
  by_cases h2 : `w2_d = fn
  · subst h2; rw [show w2Ctx.findLocalCallee? `w2_d = some "w2_d" from rfl]; simp [eq_comm]
  by_cases h3 : `w2_g = fn
  · subst h3; rw [show w2Ctx.findLocalCallee? `w2_g = some "w2_g" from rfl]; simp [eq_comm]
  by_cases h4 : `w2_h = fn
  · subst h4; rw [show w2Ctx.findLocalCallee? `w2_h = some "w2_h" from rfl]; simp [eq_comm]
  by_cases h5 : `w2_k = fn
  · subst h5; rw [show w2Ctx.findLocalCallee? `w2_k = some "w2_k" from rfl]; simp [eq_comm]
  simp only [RealBridgeCtx.findLocalCallee?, w2Ctx, w2Module, List.map, fDecl, dDecl, gDecl, hDecl, kDecl,
    u64Decl, List.find?, beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4,
    beq_false_of_ne h5]
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]

theorem w2Module_callees : ModuleCallees w2Ctx w2Module := by
  intro e he
  simp only [w2Module, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, fun fn => by rw [w2Ctx_callee]; simp [fDecl, dDecl, gDecl, hDecl, kDecl, u64Decl]⟩

/-- The caller's `let a := w2_g x` lowers to an `LNIR` `.call "w2_g"`. -/
theorem f_lowered_body :
    (lowerRealLCNFDecl w2Fuel w2Ctx fDecl "w2_f").map LNIRDecl.body =
      .ok (.letBind 1 .i64 (.call "w2_g" [0] .i64 false) (.letBind 2 .i64 (.scalar (.constU64 1))
        (.letBind 3 .i64 (.scalar (.binOp .add (.var 1) (.var 2))) (.ret 3)))) := rfl

theorem f_src :
    evalRealLCNFDecl w2Fuel w2Ctx fDecl [.u64 5] .empty (moduleFuncEnv w2Fuel w2Ctx [dDecl, gDecl, hDecl, kDecl]) =
      .ok (.u64 11, .empty) := rfl

theorem d_src :
    evalRealLCNFDecl w2Fuel w2Ctx dDecl [.u64 9, .u64 5] .empty (moduleFuncEnv w2Fuel w2Ctx [gDecl, hDecl, kDecl]) =
      .ok (.u64 4, .empty) := rfl

/-- Non-vacuity: the module lowers, `w2_f 5` evaluates to `5 * 2 + 1 = 11` through its call of `w2_g`,
    and `callRefinement` gives the lowered `w2_f` the same result. -/
theorem posWitnessCall :
    ∃ ds g, lowerRealLCNFModule w2Fuel w2Ctx w2Module = .ok ds ∧ moduleFuncTable w2Fuel ds "w2_f" = some g ∧
      evalRealLCNFDecl w2Fuel w2Ctx fDecl [.u64 5] .empty (moduleFuncEnv w2Fuel w2Ctx [dDecl, gDecl, hDecl, kDecl]) =
        .ok (.u64 11, .empty) ∧
      g [.u64 5] .empty = .ok (.u64 11, .empty) := by
  obtain ⟨ds, hds⟩ : ∃ ds, lowerRealLCNFModule w2Fuel w2Ctx w2Module = .ok ds := ⟨_, rfl⟩
  obtain ⟨-, g, hg, hfg⟩ := callRefinement _ _ _ ds w2Module_callees hds `w2_f "w2_f" _ rfl rfl
  exact ⟨ds, g, hds, hg, f_src, hfg _ _ _ f_src⟩

/-! ## Module lowerer mutants -/

/-- Post-compose the real module lowerer with a corruption of every lowered declaration. -/
def mutateModule (f : LNIRDecl → LNIRDecl) : ModuleLowerer :=
  fun fuel ctx entries => (lowerRealLCNFModule fuel ctx entries).map (List.map f)

/-- Rewrite the target and arguments of every `.call`. -/
def mapCalls (f : String → List VarId → String × List VarId) : LNIRCode → LNIRCode
  | .letBind x ty (.call s args rt ext) k => .letBind x ty (.call (f s args).1 (f s args).2 rt ext) (mapCalls f k)
  | .letBind x ty e k => .letBind x ty e (mapCalls f k)
  | .rawStore p i v ty k => .rawStore p i v ty (mapCalls f k)
  | .incRef x n k => .incRef x n (mapCalls f k)
  | .decRef x n k => .decRef x n (mapCalls f k)
  | .ite c t e => .ite c (mapCalls f t) (mapCalls f e)
  | .seqFor i lo hi a ai ty s k => .seqFor i lo hi a ai ty (mapCalls f s) (mapCalls f k)
  | .parFor o n xs ty kk k => .parFor o n xs ty kk (mapCalls f k)
  | c => c

/-- Mutant 1 (wrong call target): calls of `w2_g` go to `w2_h`. -/
def negWitnessWrongCallTarget : LNIRDecl → LNIRDecl := fun d =>
  { d with body := mapCalls (fun s args => (if s == "w2_g" then "w2_h" else s, args)) d.body }

/-- Mutant 2 (swapped call arguments): every call passes its arguments in reverse order. -/
def negWitnessSwappedCallArgs : LNIRDecl → LNIRDecl := fun d =>
  { d with body := mapCalls (fun s args => (s, args.reverse)) d.body }

/-- A module mutant is killed when, on the witness module, the lowered callee under `sym` disagrees
    with a successful source run of the callee `fn`. -/
theorem module_killed_of_run {f : LNIRDecl → LNIRDecl} (fn : Name) (sym : String) (src : FnSem)
    (args : List Val) (r r' : Val × HeapState)
    (hsrc : moduleFuncEnv w2Fuel w2Ctx (w2Module.map Prod.fst) fn = some src)
    (hloc : w2Ctx.findLocalCallee? fn = some sym) (hsrcRun : src args .empty = .ok r)
    (hrun : ∀ ds g, mutateModule f w2Fuel w2Ctx w2Module = .ok ds → moduleFuncTable w2Fuel ds sym = some g →
      g args .empty = .ok r')
    (hne : r' ≠ r) : ¬ CallRefinement (mutateModule f) := fun h => by
  obtain ⟨ds, hds⟩ : ∃ ds, mutateModule f w2Fuel w2Ctx w2Module = .ok ds := ⟨_, rfl⟩
  obtain ⟨-, g, hg, hfg⟩ := h _ _ _ ds w2Module_callees hds fn sym src hloc hsrc
  exact hne (Except.ok.inj ((hrun ds g hds hg).symm.trans (hfg _ _ _ hsrcRun)))

/-- The retargeted `w2_f` computes `w2_h 5 + 1 = 9` where the source computes `w2_g 5 + 1 = 11`. -/
theorem negWitnessWrongCallTarget_killed : ¬ CallRefinement (mutateModule negWitnessWrongCallTarget) :=
  module_killed_of_run `w2_f "w2_f" _ [.u64 5] (.u64 11, .empty) (.u64 9, .empty) rfl rfl f_src
    (fun _ _ hds hg => by cases hds; injection hg with hg; subst hg; rfl) (by simp)

/-- The swapped `w2_d` computes `w2_k 5 9 = 5 - 9` where the source computes `w2_k 9 5 = 4`. -/
theorem negWitnessSwappedCallArgs_killed : ¬ CallRefinement (mutateModule negWitnessSwappedCallArgs) :=
  module_killed_of_run `w2_d "w2_d" _ [.u64 9, .u64 5] (.u64 4, .empty) (.u64 (5 - 9), .empty) rfl rfl d_src
    (fun _ _ hds hg => by cases hds; injection hg with hg; subst hg; rfl) (by decide)

end LeanNative.Proofs.H1
