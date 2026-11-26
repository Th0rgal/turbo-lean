import LeanNative.Proofs.RealLCNFBridge.StepCases
import LeanNative.Proofs.RealLCNFBridge.CtorScalarCall
import LeanNative.IR.RealLCNFCallSemantics

/-!
# L2 helpers: environment-aware mirrors of the step-level L1 lemmas

Contract: `lean/LeanNative/Proofs/LowerCalls.lean` ("Expected helper lemmas landing with
the proofs"). `evalCodeF` and `evalStepF` mirror `evalCode`/`evalStep` clause for clause
with one new rule each, so every lemma here mirrors its L1 original with the environment
threaded through; the call rule itself is handled where the proofs consume these through
hypothesis parameters, so a sibling (L3) can instantiate the mechanical cases with its
own call rule. `evalCodeF` is well-founded-recursive (lexicographic `(Φ.length, code)`)
and its `.letBind` arm holds a dependent matcher (`match hc : FuncEnv.callTarget? …`), so
the mirrors go through the plain-match unfolding equations below instead of `dsimp`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- `evalCodeF` on a `.letBind`, as a plain (non-dependent) match on
    `FuncEnv.callTarget?` — the dependent `hc` binder in the definition exists only for
    termination, so the two forms agree. -/
theorem evalCodeF_letBind (Φ : FuncEnv) (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (ty : LNIRType) (val : LNIRExpr) (k : LNIRCode) :
    evalCodeF Φ fuel env st (.letBind dst ty val k) =
      match FuncEnv.callTarget? Φ val with
      | some ((ld, fuelD), Φ', args) =>
        match evalVarList env args with
        | .ok vals =>
          if vals.length = ld.params.length then
            match evalCodeF Φ' fuelD
                ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
                st ld.body with
            | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
            | .error err => .error err
          else .error (.typeError "call arity mismatch")
        | .error err => .error err
      | none =>
        match evalExpr env st val with
        | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
        | .error err => .error err := by
  -- `rw [eq_def]` unfolds ONLY the left-hand application (the right-hand occurrences
  -- carry different arguments, so the instantiated pattern leaves them alone; a bare
  -- `unfold` would rewrite them too and the fold-back pattern never matches).
  rw [evalCodeF.eq_def]
  try simp only []
  split <;> rename_i heq <;> simp only [heq] <;> try rfl

/-- The non-call instance of `evalCodeF_letBind`: with the environment lookup a miss the
    arm is `evalCode`'s byte for byte (modulo the recursive occurrence). -/
theorem evalCodeF_letBind_evalExpr {Φ : FuncEnv} {val : LNIRExpr}
    (hnc : FuncEnv.callTarget? Φ val = none)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (dst : VarId) (ty : LNIRType)
    (k : LNIRCode) :
    evalCodeF Φ fuel env st (.letBind dst ty val k) =
      match evalExpr env st val with
      | .ok (v, st') => evalCodeF Φ fuel (env.bind dst v) st' k
      | .error err => .error err := by
  rw [evalCodeF_letBind, hnc]

/-- Mirror of `evalCode_fuel_mono_step` (contract-named helper): the LNIR fuel is
    pass-through except for loop bounds, and a resolved call runs the callee at ITS
    entry's fuel, which does not move with the ambient fuel. -/
theorem evalCodeF_fuel_mono_step (Φ : FuncEnv) (f : Nat) :
    ∀ (c : LNIRCode) (venv : VarEnv) (hst : HeapState) (v : Val) (hst' : HeapState),
    evalCodeF Φ f venv hst c = .ok (v, hst') → evalCodeF Φ (f + 1) venv hst c = .ok (v, hst')
  | .letBind dst ty val k, venv, hst, v, hst', h => by
    rw [evalCodeF_letBind] at h ⊢
    cases hcc : FuncEnv.callTarget? Φ val with
    | none =>
      -- `cases hcc` substituted the discriminant in the goal already; reduce the
      -- resulting ground matchers on both sides.
      rw [hcc] at h
      simp only at h ⊢
      cases he : evalExpr venv hst val with
      | error _ => rw [he] at h; exact nomatch h
      | ok p =>
        rw [he] at h
        exact evalCodeF_fuel_mono_step Φ f k (venv.bind dst p.1) p.2 v hst' h
    | some pt =>
      rcases pt with ⟨⟨ld, fuelD⟩, Φ', args⟩
      rw [hcc] at h
      simp only at h ⊢
      cases hvl : evalVarList venv args with
      | error _ => rw [hvl] at h; exact nomatch h
      | ok vals =>
        rw [hvl] at h
        simp only at h ⊢
        by_cases hlen : vals.length = ld.params.length
        · rw [ite_eq_left hlen] at h ⊢
          cases hcal : evalCodeF Φ' fuelD
              ((ld.params.zip vals).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
              hst ld.body with
          | error _ => rw [hcal] at h; exact nomatch h
          | ok pr =>
            rw [hcal] at h
            exact evalCodeF_fuel_mono_step Φ f k (venv.bind dst pr.1) pr.2 v hst' h
        · rw [ite_eq_right hlen] at h; exact nomatch h
  | .rawStore pv iv vv elemTy k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hp : venv pv <;> cases hi : venv iv <;>
      cases hv : venv vv <;> simp only [hp, hi, hv] at h <;> try contradiction
    rename_i vp vi vv0
    cases vp <;> cases vi <;>
      cases vv0 <;> simp only at h ⊢ <;> try contradiction
    all_goals (
      rename_i bufId idx val
      cases hw : hst.writeElemExclusive bufId idx.toNat (maskElemVal elemTy val) <;> simp only [hw] at h ⊢
      · contradiction
      · rename_i hst1; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h)
  | .incRef ov cnt k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases he : hst.evalIncRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h
  | .decRef ov cnt k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases he : hst.evalDecRef venv ov cnt with
    | error _ => rw [he] at h; exact nomatch h
    | ok hst1 => rw [he] at h; exact evalCodeF_fuel_mono_step Φ f k venv hst1 v hst' h
  | .ite cv t e, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hc : venv cv <;> rw [hc] at h
    · exact nomatch h
    · rename_i vc; cases vc with
      | bool b => cases b <;> exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | u64 n => by_cases hn : n != 0 <;> simp only [hn, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | u256 w => by_cases hw : w != UInt256.zero <;> simp only [hw, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
          exact evalCodeF_fuel_mono_step Φ f _ venv hst v hst' h
      | _ => exact nomatch h
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    cases hlo : venv loVar <;> cases hhi : venv hiVar <;>
      cases hain : venv accInit <;> simp only [hlo, hhi, hain] at h <;> try contradiction
    rename_i vlo vhi initVal
    cases vlo <;> cases vhi <;>
      simp only at h ⊢ <;> try contradiction
    rename_i lo hi
    have hloop : ∀ cnt cur acc env0 st0 r,
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCodeF Φ f se ss stepBody) = .ok r →
        evalSeqLoop cnt cur idxVar accVar acc env0 st0 (fun se ss => evalCodeF Φ (f + 1) se ss stepBody) = .ok r := by
      intro cnt; induction cnt with
      | zero => intro _ _ _ _ _ hr; exact hr
      | succ cnt' ihc =>
        intro cur acc env0 st0 r hr; dsimp only [evalSeqLoop] at hr ⊢
        cases hs : evalCodeF Φ f ((env0.bind idxVar (.u64 cur.toUInt64)).bind accVar acc) st0 stepBody with
        | error _ => rw [hs] at hr; exact nomatch hr
        | ok pr =>
          rw [hs] at hr
          rw [evalCodeF_fuel_mono_step Φ f stepBody _ st0 pr.1 pr.2 hs]
          exact ihc (cur + 1) pr.1 env0 pr.2 r hr
    cases hl : evalSeqLoop (hi.toNat - lo.toNat) lo.toNat idxVar accVar initVal venv hst
        (fun se ss => evalCodeF Φ f se ss stepBody) with
    | error _ => rw [hl] at h; exact nomatch h
    | ok pr =>
      rw [hl] at h; rw [hloop _ _ _ _ _ pr hl]
      exact evalCodeF_fuel_mono_step Φ f k (venv.bind accVar pr.1) pr.2 v hst' h
  | .parFor outVar lenVar inputs elemTy kernel k, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢
    have hpf : ∀ r, evalParFor f venv hst lenVar inputs kernel elemTy = .ok r →
        evalParFor (f + 1) venv hst lenVar inputs kernel elemTy = .ok r := by
      intro r hp; unfold evalParFor at hp ⊢
      cases hl : venv lenVar <;> rw [hl] at hp
      · exact nomatch hp
      · rename_i vl
        cases vl with
        | u64 n =>
          dsimp only at hp ⊢
          by_cases hgt : n.toNat > f
          · simp only [hgt, ↓reduceIte] at hp; exact nomatch hp
          · have hgt' : ¬(n.toNat > f + 1) := by omega
            simp only [hgt, hgt', ↓reduceIte] at hp ⊢; exact hp
        | _ => exact nomatch hp
    cases hp : evalParFor f venv hst lenVar inputs kernel elemTy with
    | error _ => rw [hp] at h; exact nomatch h
    | ok pr =>
      rw [hp] at h; rw [hpf pr hp]
      exact evalCodeF_fuel_mono_step Φ f k (venv.bind outVar pr.1) pr.2 v hst' h
  | .ret x, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢; exact h
  | .unreachable, venv, hst, v, hst', h => by
    unfold evalCodeF at h ⊢; exact h

/-- Reserved runtime symbols `evalExpr` interprets as intrinsics (`lean_native_*`,
    `lean_mark_mt`); a lowered local callee must not shadow them (clause of
    `DeclEnvLowers` in `Proofs/LowerCalls.lean`, which uses THIS definition), so the
    `Φ`-first lookup in `evalCodeF` never captures an intrinsic call the lowering
    emitted. -/
def reservedRuntimeName (s : String) : Bool :=
  s.startsWith "lean_native_" || s == "lean_mark_mt"

/-- A name bound by no entry misses `FuncEnv.lookup?`. -/
theorem FuncEnv.lookup?_eq_none :
    ∀ (Φ : FuncEnv) (fn : String), (∀ p ∈ Φ, p.1.name ≠ fn) →
      LeanNative.Semantics.FuncEnv.lookup? Φ fn = none
  | [], _, _ => rfl
  | p :: Φ, fn, h => by
    unfold LeanNative.Semantics.FuncEnv.lookup?
    cases hbe : (p.1.name == fn) with
    | true => exact absurd (eq_of_beq hbe) (h p (.head _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact FuncEnv.lookup?_eq_none Φ fn (fun q hq => h q (.tail _ hq))

/-- A reserved runtime intrinsic (`lean_native_*`, `lean_mark_mt`) is never captured by a
    function environment whose names `DeclEnvLowers` admits (all unreserved). -/
theorem FuncEnv.callTarget?_reserved {fn : String}
    (hfn : reservedRuntimeName fn = true) {Φ : FuncEnv}
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    (args : List VarId) (ty : LNIRType) (ext : Bool) :
    LeanNative.Semantics.FuncEnv.callTarget? Φ (.call fn args ty ext) = none := by
  cases ext
  · unfold LeanNative.Semantics.FuncEnv.callTarget?
    simp only []
    rw [FuncEnv.lookup?_eq_none Φ fn
      (fun p hp heq => by have h1 := hres p hp; rw [heq, hfn] at h1; exact nomatch h1)]
    rfl
  · rfl

/-- Every `.call` that `evalExpr` interprets successfully names a reserved runtime
    intrinsic (read off its name chain: extern calls and unknown names error), so under
    `DeclEnvLowers`-admitted (unreserved) names the environment lookup misses — the
    `Φ`-first dispatch in `evalCodeF` never captures an expression the old evaluator
    succeeds on. This is the abstract-`rhs` fact the non-call let mirror consumes. -/
theorem FuncEnv.callTarget?_of_evalExpr_ok {Φ : FuncEnv}
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    {env : VarEnv} {st : HeapState} {e : LNIRExpr} {pr : Val × HeapState}
    (hok : evalExpr env st e = .ok pr) :
    LeanNative.Semantics.FuncEnv.callTarget? Φ e = none := by
  have hrn : ∀ {s L : String}, (s == L) = true → reservedRuntimeName L = true →
      reservedRuntimeName s = true := fun hbe hL => by rw [eq_of_beq hbe]; exact hL
  cases e <;> try rfl
  case call fn args ty ext =>
    cases ext
    · dsimp only [evalExpr] at hok
      cases hvl : evalVarList env args <;> rw [hvl] at hok
      · exact nomatch hok
      · simp only [Bool.false_eq_true, ↓reduceIte] at hok
        cases hc1 : (fn == "lean_native_box_u64" || fn == "lean_native_unbox_u64")
        · rw [hc1] at hok
          simp only [Bool.false_eq_true, ↓reduceIte] at hok
          cases hc2 : (fn == "lean_native_ensure_exclusive")
          · rw [hc2] at hok
            simp only [Bool.false_eq_true, ↓reduceIte] at hok
            cases hc3 : (fn == "lean_native_sarray_len")
            · rw [hc3] at hok
              simp only [Bool.false_eq_true, ↓reduceIte] at hok
              cases hc4 : (fn == "lean_mark_mt")
              · rw [hc4] at hok
                simp only [Bool.false_eq_true, ↓reduceIte] at hok
                cases hc5 : (fn == "lean_native_ctor_set" || fn == "lean_native_ctor_set_scalar")
                · rw [hc5] at hok
                  simp only [Bool.false_eq_true, ↓reduceIte] at hok
                  cases hc6 : (fn == "lean_native_ctor_set_tag")
                  · rw [hc6] at hok
                    simp only [Bool.false_eq_true, ↓reduceIte] at hok
                    cases hc7 : (fn == "lean_native_del_obj")
                    · rw [hc7] at hok
                      simp only [Bool.false_eq_true, ↓reduceIte] at hok
                      cases hc8 : (fn == "lean_native_ctor_tag")
                      · rw [hc8] at hok
                        simp only [Bool.false_eq_true, ↓reduceIte] at hok
                        exact nomatch hok
                      · exact FuncEnv.callTarget?_reserved
                          (hrn hc8 (by first | rfl | decide | simp [reservedRuntimeName]))
                          hres args ty false
                    · exact FuncEnv.callTarget?_reserved
                        (hrn hc7 (by first | rfl | decide | simp [reservedRuntimeName]))
                        hres args ty false
                  · exact FuncEnv.callTarget?_reserved
                      (hrn hc6 (by first | rfl | decide | simp [reservedRuntimeName]))
                      hres args ty false
                · rcases (Bool.or_eq_true _ _).mp hc5 with hbe | hbe
                  · exact FuncEnv.callTarget?_reserved
                      (hrn hbe (by first | rfl | decide | simp [reservedRuntimeName]))
                      hres args ty false
                  · exact FuncEnv.callTarget?_reserved
                      (hrn hbe (by first | rfl | decide | simp [reservedRuntimeName]))
                      hres args ty false
              · exact FuncEnv.callTarget?_reserved
                  (hrn hc4 (by first | rfl | decide | simp [reservedRuntimeName]))
                  hres args ty false
            · exact FuncEnv.callTarget?_reserved
                (hrn hc3 (by first | rfl | decide | simp [reservedRuntimeName]))
                hres args ty false
          · exact FuncEnv.callTarget?_reserved
              (hrn hc2 (by first | rfl | decide | simp [reservedRuntimeName]))
              hres args ty false
        · rcases (Bool.or_eq_true _ _).mp hc1 with hbe | hbe
          · exact FuncEnv.callTarget?_reserved
              (hrn hbe (by first | rfl | decide | simp [reservedRuntimeName]))
              hres args ty false
          · exact FuncEnv.callTarget?_reserved
              (hrn hbe (by first | rfl | decide | simp [reservedRuntimeName]))
              hres args ty false
    · rfl

/-- Mirror of `allocZeroScalarSlotsPure_rel`'s wrap conjunct carrier at a fixed `Φ`: the
    zero-slot wrapper peels through `evalCodeF` exactly as through `evalCode`, because
    every wrapped binding is a `.scalar` expression (`callTarget?` misses by `rfl`). -/
theorem allocZeroScalarSlotsPure_relF (Φ : FuncEnv) :
    ∀ (slots : List (Option Nat × LNIRType)) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv)
      (fuel : Nat) (hst : HeapState),
      BridgeStateInv st lenv venv →
      ∃ venvZ,
        BridgeStateInv (allocZeroScalarSlotsPure st slots).2 lenv venvZ ∧
        (∀ u, u < st.nextVarId → venvZ u = venv u) ∧
        evalVarList venvZ ((allocZeroScalarSlotsPure st slots).1.map Prod.fst) =
          .ok (slots.map fun _ => Val.u64 0) ∧
        ∀ body, evalCodeF Φ (fuel + 1) venv hst
            (wrapZeroScalarSlotsPure (allocZeroScalarSlotsPure st slots).1 body) =
          evalCodeF Φ (fuel + 1) venvZ hst body
  | [], st, _, venv, _, _, hinv =>
    ⟨venv, hinv, fun _ _ => rfl, rfl, fun _ => rfl⟩
  | (_, sTy) :: rest, st, lenv, venv, fuel, hst, hinv => by
    dsimp only [allocZeroScalarSlotsPure, wrapZeroScalarSlotsPure]
    rcases freshVar_spec st sTy with ⟨hfv1, hfvNext, _, _, _, _⟩
    let z := (st.freshVar sTy).1
    let st1 := (st.freshVar sTy).2
    let venv1 := venv.bind z (.u64 0)
    have hinv1 : BridgeStateInv st1 lenv venv1 :=
      bridgeInv_freshVar st lenv venv sTy (.u64 0) hinv
    rcases allocZeroScalarSlotsPure_relF Φ rest st1 lenv venv1 fuel hst hinv1 with
      ⟨venvZ, hinvZ, hagree1, hvlRest, hwrapRest⟩
    have hzLt1 : z < st1.nextVarId := by
      dsimp only [z, st1]; rw [hfv1, hfvNext]; exact Nat.lt_succ_self _
    have hzZ : venvZ z = some (.u64 0) :=
      (hagree1 z hzLt1).trans (VarEnv.bind_self venv z (.u64 0))
    refine ⟨venvZ, hinvZ, fun u hu => ?_, ?_, fun body => ?_⟩
    · have huLtZ : u < z := by dsimp only [z]; rw [hfv1]; exact hu
      have huLt1 : u < st1.nextVarId := Nat.lt_trans huLtZ hzLt1
      exact (hagree1 u huLt1).trans (venv_bind_fresh venv z u huLtZ (.u64 0))
    · dsimp only [List.map, evalVarList]
      rw [hzZ, hvlRest]
    · rw [evalCodeF_letBind_evalExpr rfl]
      dsimp only [evalExpr, evalScalarExpr]
      exact hwrapRest body

/-- Mirror of `evalCode_ite_asBool` (JpTag) at a fixed `Φ`. -/
private theorem evalCodeF_ite_asBool (Φ : FuncEnv) (fuel : Nat) (venv : VarEnv) (hst : HeapState)
    (condVar : VarId) (cond : Val) (b : Bool) (thenB elseB : LNIRCode)
    (hcond : venv condVar = some cond) (hb : asBool cond = .ok b) :
    evalCodeF Φ fuel venv hst (.ite condVar thenB elseB) =
      if b then evalCodeF Φ fuel venv hst thenB else evalCodeF Φ fuel venv hst elseB := by
  rw [evalCodeF.eq_def]
  simp only []
  rw [hcond]
  cases cond with
  | bool b0 =>
    injection hb with heq; subst b0
    cases b <;> rfl
  | u64 n => injection hb with heq; subst b; rfl
  | u256 w => injection hb with heq; subst b; rfl
  | _ => exact nomatch hb

/-- Mirror of `tag_branch_sound` (JpTag) with both environments threaded: the branch
    continuations now evaluate under `evalStepF Δ` on the source side and the lowered
    branch code under `evalCodeF Φ`; the lowering side is unchanged. -/
theorem tag_branch_soundF (Δ : DeclEnv) (Φ : FuncEnv)
    (fuel : Nat) (ctx : RealBridgeCtx) (lenv envIn : LEnv)
    (venv : VarEnv) (hst hst' : HeapState) (v cond : Val)
    (condVar : VarId) (condTy : LNIRType) (cidx : Nat) (isBool : Bool) (idx : Nat)
    (discr? : Option Lean.FVarId) (rest : List (Lean.Compiler.LCNF.Alt .impure))
    (altCode : Lean.Compiler.LCNF.Code .impure)
    (yesCode noCode code : LNIRCode) (st2 st' : RealBridgeState)
    (hi1 : lnirTypeEq condTy .i1 = true → isBool = true)
    (hcondV : venv condVar = some cond)
    (hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
      evalStepF Δ fuel ctx envIn hst (.inl altCode) = .ok (v, hst') →
      evalCodeF Φ (fuel + 1) venvY hst yesCode = .ok (v, hst'))
    (hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
      evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest)) = .ok (v, hst') →
      evalCodeF Φ (fuel + 1) venvN hst noCode = .ok (v, hst'))
    (hbr : (if isBool || lnirTypeEq condTy .i1 then
        (Except.ok ((lowerTagBranchPure condVar condTy cidx isBool 0 yesCode noCode).1, st2) :
          Except String (LNIRCode × RealBridgeState))
      else
        Except.ok ((lowerTagBranchPure condVar condTy cidx isBool (st2.freshVar .i1).1 yesCode noCode).1,
          (st2.freshVar .i1).2)) = Except.ok (code, st'))
     (hev : (if isBool then
         match asBool cond with
         | .ok b =>
           if cidx == 0 then
             if b then evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
             else evalStepF Δ fuel ctx envIn hst (.inl altCode)
           else if cidx == 1 then
             if b then evalStepF Δ fuel ctx envIn hst (.inl altCode)
             else evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
           else evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
         | .error e => .error e
       else
         match cond with
         | .u64 n =>
           if n == cidx.toUInt64 then evalStepF Δ fuel ctx envIn hst (.inl altCode)
           else evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, rest))
         | _ => .error (.typeError "evalBinOp: invalid operand types")) = .ok (v, hst')) :
     evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  cases isBool
  · have hnotI1 : lnirTypeEq condTy .i1 = false := by
      cases h : lnirTypeEq condTy .i1
      · rfl
      · exact nomatch hi1 h
    rw [hnotI1] at hbr
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, lowerTagBranchPure, hnotI1] at hbr hev
    injection hbr with hp; rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    cases cond with
    | u64 n =>
      rw [evalCodeF_letBind_evalExpr rfl]
      rw [(freshVar_spec st2 .i1).1]
      dsimp only [evalExpr, evalScalarExpr]; rw [hcondV]; dsimp only [evalBinOp, ↓reduceIte]
      let cmpVar := st2.nextVarId
      cases hn : (n == cidx.toUInt64) <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at hev ⊢
      · rw [evalCodeF.eq_def]; simp only []
        rw [VarEnv.bind_self]
        exact hno (venv.bind cmpVar (.bool false))
          (fun u hu => venv_bind_fresh venv cmpVar u hu (.bool false)) hev
      · rw [evalCodeF.eq_def]; simp only []
        rw [VarEnv.bind_self]
        exact hyes (venv.bind cmpVar (.bool true))
          (fun u hu => venv_bind_fresh venv cmpVar u hu (.bool true)) hev
    | _ => exact nomatch hev
  · simp only [Bool.true_or, ↓reduceIte, lowerTagBranchPure] at hbr hev
    injection hbr with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
    cases hab : asBool cond with
    | error _ => rw [hab] at hev; exact nomatch hev
    | ok b =>
      rw [hab] at hev
      cases hc0 : (cidx == 0)
      · simp only [hc0, Bool.false_eq_true, ↓reduceIte] at hev ⊢
        cases hc1 : (cidx == 1)
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hev ⊢
          exact hno venv (fun _ _ => rfl) hev
        · simp only [hc1, ↓reduceIte] at hev ⊢
          rw [evalCodeF_ite_asBool Φ (fuel + 1) venv hst condVar cond b yesCode noCode hcondV hab]
          cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hev ⊢
          · exact hno venv (fun _ _ => rfl) hev
          · exact hyes venv (fun _ _ => rfl) hev
      · simp only [hc0, ↓reduceIte] at hev ⊢
        rw [evalCodeF_ite_asBool Φ (fuel + 1) venv hst condVar cond b noCode yesCode hcondV hab]
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hev ⊢
        · exact hyes venv (fun _ _ => rfl) hev
        · exact hno venv (fun _ _ => rfl) hev

/-- Mirror of `lowerStepInr_sound` (StepCases) with both environments threaded; the
    induction hypothesis is a parameter exactly as in L1, so the call rule never appears
    here — a sibling instantiates it with its own `ih`. -/
theorem lowerStepInr_soundF (Δ : DeclEnv) (Φ : FuncEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (condVar : VarId) (isBool : Bool) (idx : Nat) (discr? : Option Lean.FVarId)
    (alts : List (Lean.Compiler.LCNF.Alt .impure)) (code : LNIRCode) (cond : Val)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inr (condVar, isBool, idx, discr?, alts)) = .ok (code, st'))
    (hcondLt : condVar < st.nextVarId)
    (hdiscr : ∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true)
    (hi1 : lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true)
    (hcondV : venv condVar = some cond)
    (h_eval : evalStepF Δ (fuel + 1) ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  rw [evalStepF.eq_def] at h_eval
  simp only at h_eval
  cases alts with
  | nil => exact nomatch h_eval
  | cons alt rest =>
    cases rest with
    | nil =>
      cases alt with
      | alt cn ps c _ =>
        dsimp only at h_lower h_eval
        cases hemp : (!ps.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h_lower
        · exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
            (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
        · exact nomatch h_lower
      | ctorAlt info c _ =>
        dsimp only at h_lower h_eval
        rcases discr_env_inv st lenv venv discr? info.name hinv hdiscr with ⟨hinvIn, _⟩
        change (match lowerImpureStepPure fuel ctx
            (match discr?.bind st.lookupFVar? with
             | some dv => st.setActiveCtor dv info.name | none => st)
            (.inl c) with
          | Except.ok (c0, stOut) =>
            Except.ok (c0, ({ stOut with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls } : RealBridgeState))
          | Except.error e => Except.error e) = Except.ok (code, st') at h_lower
        cases hc : lowerImpureStepPure fuel ctx
            (match discr?.bind st.lookupFVar? with
             | some dv => st.setActiveCtor dv info.name | none => st)
            (.inl c) with
        | error _ => rw [hc] at h_lower; exact nomatch h_lower
        | ok pr =>
          rw [hc] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
          exact evalCodeF_fuel_mono_step Φ fuel pr.1 venv hst v hst'
            (ih _ pr.2 _ venv hst hst' v (.inl c) pr.1 hinvIn hc h_eval)
      | default c =>
        exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
          (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
    | cons alt2 rest2 =>
      cases alt with
      | default c =>
        exact evalCodeF_fuel_mono_step Φ fuel code venv hst v hst'
          (ih st st' lenv venv hst hst' v (.inl c) code hinv h_lower h_eval)
      | ctorAlt info c _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        dsimp only at h_eval
        rcases discr_env_inv st lenv venv discr? info.name hinv hdiscr with ⟨hinvIn, hnextIn, htyIn⟩
        cases hD : discr?.bind st.lookupFVar? with
        | none =>
          rw [hD] at h_lower hinvIn hnextIn htyIn; dsimp only at h_lower hinvIn hnextIn htyIn
          cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hn1 (fun u hu => ht1 u hu) rfl (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, _⟩
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hn1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStepF Δ fuel ctx
                    (match discr? with
                     | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                     | none => lenv)
                    hst (.inl c) = .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCodeF_fuel_mono_step Φ fuel yesCode venvY hst v hst'
                  (ih st st1 _ venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree st _ venv venvY hinvIn
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCodeF_fuel_mono_step Φ fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hn1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_soundF Δ Φ fuel ctx lenv
                (match discr? with
                 | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                 | none => lenv)
                venv hst hst' v cond condVar
                (st.getVarType condVar) info.cidx isBool idx discr? (alt2 :: rest2) c
                yesCode noCode code st2 st' hi1 hcondV hyes hno h_lower h_eval
        | some dv =>
          rw [hD] at h_lower hinvIn hnextIn htyIn; dsimp only at h_lower hinvIn hnextIn htyIn
          let stIn := st.setActiveCtor dv info.name
          cases h1 : lowerImpureStepPure fuel ctx stIn (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx stIn st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hbase1 : st.nextVarId ≤ st1.nextVarId := hn1
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hbase1
                (fun u hu => ht1 u hu) rfl (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, _⟩
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hbase1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStepF Δ fuel ctx
                    (match discr? with
                     | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                     | none => lenv)
                    hst (.inl c) = .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCodeF_fuel_mono_step Φ fuel yesCode venvY hst v hst'
                  (ih stIn st1 _ venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree stIn _ venv venvY hinvIn
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCodeF_fuel_mono_step Φ fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hbase1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_soundF Δ Φ fuel ctx lenv
                (match discr? with
                 | some dx => if (lenv.vals dx).isSome then lenv.withCtor dx info.name else lenv
                 | none => lenv)
                venv hst hst' v cond condVar
                (st.getVarType condVar) info.cidx isBool idx discr? (alt2 :: rest2) c
                yesCode noCode code st2 st' hi1 hcondV hyes hno h_lower h_eval
      | alt ctorName params c _ =>
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw,
          MonadExceptOf.throw, throwThe] at h_lower
        dsimp only at h_eval
        cases hemp : (!params.isEmpty) <;> simp only [hemp, ↓reduceIte, Bool.false_eq_true] at h_lower
        · cases h1 : lowerImpureStepPure fuel ctx st (.inl c) with
          | error _ => rw [h1] at h_lower; exact nomatch h_lower
          | ok p1 =>
            rw [h1] at h_lower; rcases p1 with ⟨yesCode, st1⟩; dsimp only at h_lower
            rcases lowerImpureStepPure_mono fuel ctx st st1 (.inl c) yesCode h1 with ⟨hn1, ht1⟩
            have hinv1R : BridgeStateInv
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                lenv venv :=
              bridgeInv_ext st _ lenv venv hinv hn1
                (fun u hu => by change st1.getVarType u = st.getVarType u; exact ht1 u hu) rfl
                (fun _ _ => rfl) rfl
            cases h2 : lowerImpureStepPure fuel ctx
                { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) with
            | error _ => rw [h2] at h_lower; exact nomatch h_lower
            | ok p2 =>
              rw [h2] at h_lower; rcases p2 with ⟨noCode, st2⟩; dsimp only at h_lower
              rcases lowerImpureStepPure_mono fuel ctx
                  { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                  st2 (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode h2 with ⟨hn2, ht2⟩
              have hcondLt2 : condVar < st2.nextVarId := Nat.lt_of_lt_of_le hcondLt (Nat.le_trans hn1 hn2)
              have hgeBase : st.nextVarId ≤ st2.nextVarId := Nat.le_trans hn1 hn2
              have hyes : ∀ venvY, (∀ u, u < st2.nextVarId → venvY u = venv u) →
                  evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvY hst yesCode = .ok (v, hst') := by
                intro venvY hge hev
                exact evalCodeF_fuel_mono_step Φ fuel yesCode venvY hst v hst'
                  (ih st st1 lenv venvY hst hst' v (.inl c) yesCode
                    (bridgeInv_venv_agree st lenv venv venvY hinv
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hgeBase))) h1 hev)
              have hno : ∀ venvN, (∀ u, u < st2.nextVarId → venvN u = venv u) →
                  evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx + 1, discr?, alt2 :: rest2)) =
                    .ok (v, hst') →
                  evalCodeF Φ (fuel + 1) venvN hst noCode = .ok (v, hst') := by
                intro venvN hge hev
                exact evalCodeF_fuel_mono_step Φ fuel noCode venvN hst v hst'
                  (ih { st1 with fvarMap := st.fvarMap, activeCtor := st.activeCtor, jpDecls := st.jpDecls }
                    st2 lenv venvN hst hst' v
                    (.inr (condVar, isBool, idx + 1, discr?, alt2 :: rest2)) noCode
                    (bridgeInv_venv_agree _ lenv venv venvN hinv1R
                      (fun u hu => hge u (Nat.lt_of_lt_of_le hu hn2))) h2
                    ⟨Nat.lt_of_lt_of_le hcondLt hn1, fun dx hdx => by
                      have := hdiscr dx hdx
                      change (st.lookupFVar? dx).isSome = true at this
                      simp only [RealBridgeState.lookupFVar?]; exact this,
                     fun h => hi1 (by
                       have hty1R : st1.getVarType condVar = st.getVarType condVar := ht1 condVar hcondLt
                       change lnirTypeEq (st1.getVarType condVar) .i1 = true at h
                       rw [hty1R] at h; exact h),
                     cond, by rw [hge condVar (Nat.lt_of_lt_of_le hcondLt hgeBase)]; exact hcondV, hev⟩)
              exact tag_branch_soundF Δ Φ fuel ctx lenv lenv venv hst hst' v cond condVar
                (st.getVarType condVar) ((ctx.findNullaryCtor? ctorName).getD idx) isBool idx discr?
                (alt2 :: rest2) c yesCode noCode code st2 st' hi1 hcondV hyes hno
                h_lower h_eval
        · exact nomatch h_lower

/-- Mirror of `evalCtorWriteStep_sound` (StepCases) at a fixed `Φ` with
    `DeclEnvLowers`-admitted names: the two wrapped bindings peel through the unfolding
    equation (`.scalar` by `rfl`, the `lean_native_ctor_set*` intrinsic by the
    reserved-name non-capture fact). -/
theorem evalCtorWriteStep_soundF (Φ : FuncEnv)
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    (fuel : Nat) (st : RealBridgeState) (venv : VarEnv)
    (hst hst1 hst' : HeapState) (v : Val) (objVid valVid : VarId) (objId : Nat)
    (slot : Nat) (yVal : Val) (isObj : Bool) (kCode : LNIRCode)
    (hobjLt : objVid < st.nextVarId) (hvalLt : valVid < st.nextVarId)
    (hvalV : venv objVid = some (.objPtr objId)) (hyValV : venv valVid = some yVal)
    (hwf : writeField hst objId (slot.toUInt64).toNat yVal isObj = .ok hst1)
    (hkEval : evalCodeF Φ (fuel + 1)
      ((venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)).bind ((st.freshVar .i64).2.freshVar .unit).1 .unit)
      hst1 kCode = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst
      (.letBind (st.freshVar .i64).1 .i64 (.scalar (.constU64 slot.toUInt64))
        (.letBind ((st.freshVar .i64).2.freshVar .unit).1 .unit
          (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
            [objVid, (st.freshVar .i64).1, valVid] .unit false) kCode)) =
      .ok (v, hst') := by
  have hidxId : (st.freshVar .i64).1 = st.nextVarId := (freshVar_spec st .i64).1
  have hobjV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) objVid = some (.objPtr objId) := by
    rw [hidxId, venv_bind_fresh venv st.nextVarId objVid hobjLt]
    exact hvalV
  have hvalV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) valVid = some yVal := by
    rw [hidxId, venv_bind_fresh venv st.nextVarId valVid hvalLt]
    exact hyValV
  have hidxV1 : (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) (st.freshVar .i64).1 =
      some (.u64 slot.toUInt64) :=
    VarEnv.bind_self _ _ _
  have hvl : evalVarList (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64))
      [objVid, (st.freshVar .i64).1, valVid] =
      .ok [.objPtr objId, .u64 slot.toUInt64, yVal] := by
    simp only [evalVarList, hobjV1, hidxV1, hvalV1]
  have hcall : evalExpr (venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)) hst
      (.call (if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
        [objVid, (st.freshVar .i64).1, valVid] .unit false) = .ok (.unit, hst1) := by
    cases isObj
    · dsimp only [Bool.false_eq_true, ↓reduceIte, evalExpr]
      rw [hvl]
      change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal false).map (Val.unit, ·) =
        .ok (Val.unit, hst1)
      unfold writeField at hwf
      rw [hwf]; rfl
    · dsimp only [↓reduceIte, evalExpr]
      rw [hvl]
      change (hst.writeHeapObjFieldExclusive objId (slot.toUInt64).toNat yVal true).map (Val.unit, ·) =
        .ok (Val.unit, hst1)
      unfold writeField at hwf
      rw [hwf]; rfl
  rw [evalCodeF_letBind_evalExpr rfl]
  dsimp only [evalExpr, evalScalarExpr]
  rw [evalCodeF_letBind_evalExpr
    (FuncEnv.callTarget?_reserved
      (fn := if isObj then "lean_native_ctor_set" else "lean_native_ctor_set_scalar")
      (by cases isObj <;> first | rfl | decide | simp [reservedRuntimeName]) hres
      [objVid, (st.freshVar .i64).1, valVid] .unit false)]
  rw [hcall]
  exact hkEval

/-- Mirror of `lowerSetTag_sound` (CtorScalarCall) with both environments threaded. -/
theorem lowerSetTag_soundF (Δ : DeclEnv) (Φ : FuncEnv)
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (x : Lean.FVarId) (cidx : Nat) (k : Lean.Compiler.LCNF.Code .impure)
    (himp : Lean.Compiler.LCNF.Purity.impure = .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inl (.setTag x cidx k himp)) = .ok (code, st'))
    (h_eval : evalStepF Δ (fuel + 1) ctx lenv hst (.inl (.setTag x cidx k himp)) = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  rw [evalStepF.eq_def] at h_eval
  simp only at h_eval
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
  cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
  · exact nomatch h_lower
  · rename_i objVid; dsimp only at h_lower
    rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with
      ⟨hluX, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
    rw [hvalL] at h_eval
    cases hhp : (!(ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid))) <;>
      simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
    · have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
        dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
      rw [hresEq] at h_eval
      let nextCtor? : Option Lean.Name :=
        match st.resolveHeapCtor? ctx objVid x with
        | some cur => if ctx.hasSiblingEntry cur then ctx.findSiblingCtor? cur cidx else none
        | none => none
      let st1 := st.setActiveCtorOpt objVid nextCtor?
      let st2 := (st1.freshVar .i64).2
      let st3 := (st2.freshVar .unit).2
      have h_lower' :
          ∃ pk, lowerImpureStepPure fuel ctx st3 (.inl k) = .ok pk ∧
            code = .letBind (st1.freshVar .i64).1 .i64 (.scalar (.constU64 cidx.toUInt64))
              (.letBind (st2.freshVar .unit).1 .unit
                (.call "lean_native_ctor_set_tag" [objVid, (st1.freshVar .i64).1] .unit false) pk.1) ∧
            st' = pk.2 := by
        dsimp only [st1, st2, st3, nextCtor?]
        cases hrc : st.resolveHeapCtor? ctx objVid x
        · rw [hrc] at h_lower; dsimp only at h_lower ⊢
          cases hk : lowerImpureStepPure fuel ctx
              (((st.setActiveCtorOpt objVid none).freshVar .i64).2.freshVar .unit).2 (.inl k)
          · rw [hk] at h_lower; exact nomatch h_lower
          · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
            exact ⟨_, rfl, hc.symm, hs.symm⟩
        · rename_i cur
          rw [hrc] at h_lower; dsimp only at h_lower ⊢
          cases hhs : ctx.hasSiblingEntry cur
          · rw [hhs] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower ⊢
            cases hk : lowerImpureStepPure fuel ctx
                (((st.setActiveCtorOpt objVid none).freshVar .i64).2.freshVar .unit).2 (.inl k)
            · rw [hk] at h_lower; exact nomatch h_lower
            · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
              exact ⟨_, rfl, hc.symm, hs.symm⟩
          · rw [hhs] at h_lower; simp only [↓reduceIte] at h_lower ⊢
            cases hfs : ctx.findSiblingCtor? cur cidx
            · rw [hfs] at h_lower; exact nomatch h_lower
            · rename_i nextC
              rw [hfs] at h_lower; dsimp only at h_lower ⊢
              cases hk : lowerImpureStepPure fuel ctx
                  (((st.setActiveCtorOpt objVid (some nextC)).freshVar .i64).2.freshVar .unit).2 (.inl k)
              · rw [hk] at h_lower; exact nomatch h_lower
              · rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hc, hs⟩
                exact ⟨_, rfl, hc.symm, hs.symm⟩
      rcases h_lower' with ⟨pk, hk, rfl, rfl⟩
      cases val with
      | objPtr objId =>
        dsimp only at h_eval
        change (match hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
          | .ok st' => evalStepF Δ fuel ctx (lenv.withCtorOpt x nextCtor?) st' (.inl k)
          | .error e => .error e) = .ok (v, hst') at h_eval
        cases hset : hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat with
        | error _ => rw [hset] at h_eval; exact nomatch h_eval
        | ok hst1 =>
          rw [hset] at h_eval
          have hst1Next : st1.nextVarId = st.nextVarId := by
            dsimp only [st1]; cases nextCtor? <;> rfl
          have hinv1 : BridgeStateInv st1 (lenv.withCtorOpt x nextCtor?) venv :=
            bridgeInv_setActiveCtorOpt st lenv venv objVid nextCtor? x hinv hluX
          have hinv3 : BridgeStateInv st3 (lenv.withCtorOpt x nextCtor?)
              ((venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)).bind (st2.freshVar .unit).1 .unit) :=
            bridgeInv_freshVar st2 (lenv.withCtorOpt x nextCtor?)
              (venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)) .unit .unit
              (bridgeInv_freshVar st1 (lenv.withCtorOpt x nextCtor?) venv .i64 (.u64 cidx.toUInt64) hinv1)
          have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1
              ((venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)).bind (st2.freshVar .unit).1 .unit)
              hst1 v hst'
            (ih st3 pk.2 (lenv.withCtorOpt x nextCtor?)
              ((venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)).bind (st2.freshVar .unit).1 .unit)
              hst1 hst' v (.inl k) pk.1 hinv3 hk h_eval)
          have htagId : (st1.freshVar .i64).1 = st.nextVarId :=
            (freshVar_spec st1 .i64).1.trans hst1Next
          have hobjV1 : (venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)) objVid =
              some (.objPtr objId) := by
            rw [htagId, venv_bind_fresh venv st.nextVarId objVid hobjLt]; exact hvalV
          have htagV1 : (venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)) (st1.freshVar .i64).1 =
              some (.u64 cidx.toUInt64) :=
            VarEnv.bind_self _ _ _
          have hcall : evalExpr (venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64)) hst
              (.call "lean_native_ctor_set_tag" [objVid, (st1.freshVar .i64).1] .unit false) =
              .ok (.unit, hst1) := by
            have hvl : evalVarList (venv.bind (st1.freshVar .i64).1 (.u64 cidx.toUInt64))
                [objVid, (st1.freshVar .i64).1] =
                .ok [.objPtr objId, .u64 cidx.toUInt64] := by
              simp only [evalVarList, hobjV1, htagV1]
            dsimp only [evalExpr]; rw [hvl]
            change (hst.setHeapObjTagExclusive objId (cidx.toUInt64).toNat).map (Val.unit, ·) =
              .ok (Val.unit, hst1)
            rw [hset]; rfl
          rw [evalCodeF_letBind_evalExpr rfl]
          dsimp only [evalExpr, evalScalarExpr]
          rw [evalCodeF_letBind_evalExpr
            (FuncEnv.callTarget?_reserved (fn := "lean_native_ctor_set_tag")
              (by first | rfl | decide | simp [reservedRuntimeName]) hres
              [objVid, (st1.freshVar .i64).1] .unit false)]
          rw [hcall]
          exact hkEval
      | _ => exact nomatch h_eval
    · exact nomatch h_lower

/-- Mirror of `lowerLetNonScalarCtor_sound` (CtorScalarCall) with both environments.
    `hnc_src` is the source-side callTarget? miss (supplied by each caller: `rfl` for a
    non-`fap` value, the caller-map miss for a `fap` the lowering did not treat as a local
    call); the target-side miss for the abstract right-hand side comes from
    `FuncEnv.callTarget?_of_evalExpr_ok`. -/
private theorem lowerLetNonScalarCtor_soundF (Δ : DeclEnv) (Φ : FuncEnv)
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (hnoScCtor : ∀ info args h, decl.value = .ctor info args h →
      (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0)) = false)
    (hnc_src : LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget? Δ ctx decl.value = none)
    (h_lower : (do
      let rawDeclTy := lowerGroundImpureTypeWith ctx decl.type
      let (rhs, st1) ← lowerImpureLetValuePure ctx st decl.value rawDeclTy
      let isBox := match decl.value with | .box _ _ _ => true | _ => false
      let ty := inferImpureRhsTypePure st1 rhs rawDeclTy isBox
      let (dst, st2) := st1.allocFreshFVar decl.fvarId ty
      let st2' := match decl.value with
        | .ctor info _ _ => if lnirTypeEq ty .objPtr then st2.setActiveCtor dst info.name else st2
        | _ => st2
      match rhs with
      | .isExclusive _ =>
        let (exclVar, st3) := st2'.freshVar .i1
        let (kCode, st4) ← lowerImpureStepPure fuel ctx st3 (.inl k)
        return (.letBind exclVar .i1 rhs (.letBind dst .i1 (.scalar (.unaryOp .not (.var exclVar))) kCode), st4)
      | _ =>
        let (kCode, st3) ← lowerImpureStepPure fuel ctx st2' (.inl k)
        return (.letBind dst ty rhs kCode, st3) : Except String (LNIRCode × RealBridgeState)) = .ok (code, st'))
    (h_eval : evalStepF Δ (fuel + 1) ctx lenv hst (.inl (.let decl k)) = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  rw [evalStepF.eq_def] at h_eval
  simp only at h_eval
  -- the dependent callTarget? matcher: refute the some-branch with `hnc_src`
  split at h_eval
  · rename_i heq
    rw [hnc_src] at heq
    exact nomatch heq
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
  let rawDeclTy := lowerGroundImpureTypeWith ctx decl.type
  cases hl : lowerImpureLetValuePure ctx st decl.value rawDeclTy with
  | error _ => rw [hl] at h_lower; exact nomatch h_lower
  | ok pl =>
    rw [hl] at h_lower; rcases pl with ⟨rhs, st1⟩
    cases hev : evalLetValue ctx lenv hst decl.value rawDeclTy with
    | error _ => rw [hev] at h_eval; exact nomatch h_eval
    | ok pev =>
      rw [hev] at h_eval; rcases pev with ⟨val, hst1, ctor?⟩; dsimp only at h_eval h_lower
      have hst1Eq := lowerImpureLetValuePure_st_eq ctx st st1 decl.value rawDeclTy rhs hl
      subst st1
      rcases lowerImpureLetValuePure_sound ctx st lenv venv hst hst1 decl.value rawDeclTy rhs st val ctor?
          hnoScCtor hinv hl hev with ⟨_, hrhsEval, htyEq, hctorEq⟩
      let ty := inferImpureRhsTypePure st rhs rawDeclTy
        (match decl.value with | .box _ _ _ => true | _ => false)
      have hEvalK : evalStepF Δ fuel ctx
          (lenv.bind decl.fvarId val
            (match decl.value with | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none | _ => none)
            (some ty))
          hst1 (.inl k) = .ok (v, hst') := by
        have htyEq' : ty = _ := htyEq
        have hEqEnv :
            lenv.bind decl.fvarId val
              (match decl.value with
               | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none
               | _ => none)
              (some ty) = _ :=
          congrArg (fun t =>
            lenv.bind decl.fvarId val
              (match decl.value with
               | .ctor _ _ _ => if lnirTypeEq t .objPtr then ctor? else none
               | _ => none)
              (some t)) htyEq'
        rw [hEqEnv]; exact h_eval
      let st2 := (st.allocFreshFVar decl.fvarId ty).2
      let dst := (st.allocFreshFVar decl.fvarId ty).1
      have hinv2 : BridgeStateInv st2 (lenv.bind decl.fvarId val none (some ty)) (venv.bind dst val) :=
        bridgeInv_bind_fresh st lenv venv decl.fvarId ty val hinv
      let st2' := match decl.value with
        | .ctor info _ _ => if lnirTypeEq ty .objPtr then st2.setActiveCtor dst info.name else st2
        | _ => st2
      let storedCtor := match decl.value with
        | .ctor _ _ _ => if lnirTypeEq ty .objPtr then ctor? else none
        | _ => none
      have hinv2' : BridgeStateInv st2' (lenv.bind decl.fvarId val storedCtor (some ty)) (venv.bind dst val) := by
        dsimp only [st2', storedCtor]
        cases hdv : decl.value with
        | ctor info args hh =>
          dsimp only
          cases hobj : lnirTypeEq ty .objPtr
          · simp only [Bool.false_eq_true, ↓reduceIte]; exact hinv2
          · simp only [↓reduceIte]
            have hct : ctor? = some info.name := by
              apply hctorEq info args hh hdv
              dsimp only [ty] at hobj; rw [hdv] at hobj; exact hobj
            rw [hct, ← lenv_bind_withCtor]
            have hluDst : st2.lookupFVar? decl.fvarId = some dst := by
              dsimp only [st2, dst]; rw [lookupFVar_allocFresh, beq_self_eq_true]; rfl
            exact bridgeInv_setActiveCtor st2 (lenv.bind decl.fvarId val none (some ty))
              (venv.bind dst val) dst info.name decl.fvarId hinv2 hluDst
        | _ => exact hinv2
      have hst2Next : st2'.nextVarId = st.nextVarId + 1 := by
        dsimp only [st2']; cases decl.value <;> try rfl
        cases lnirTypeEq ty .objPtr <;> rfl
      clear hl htyEq hctorEq
      cases rhs with
      | isExclusive objVar =>
        dsimp only at h_lower hrhsEval
        rcases hrhsEval with ⟨b, hexclEval, rfl⟩
        split at h_lower
        · exact nomatch h_lower
        · rename_i pk hk
          injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hcodeEq, _⟩
          have hkClean : lowerImpureStepPure fuel ctx (st2'.freshVar .i1).2 (.inl k) = .ok pk := hk
          have hexclId : (st2'.freshVar .i1).1 = st2'.nextVarId := (freshVar_spec st2' .i1).1
          have hne : st2'.nextVarId ≠ dst := by
            change st2'.nextVarId ≠ st.nextVarId
            rw [hst2Next]; exact Nat.ne_of_gt (Nat.lt_succ_self _)
          have hinv3 : BridgeStateInv (st2'.freshVar .i1).2
              (lenv.bind decl.fvarId (.bool (!b)) storedCtor (some ty))
              ((venv.bind (st2'.freshVar .i1).1 (.bool b)).bind dst (.bool (!b))) := by
            rw [hexclId, varEnv_bind_comm venv st2'.nextVarId dst (.bool b) (.bool (!b)) hne, ← hexclId]
            exact bridgeInv_freshVar st2' _ (venv.bind dst (.bool (!b))) .i1 (.bool b) hinv2'
          have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst1 v hst'
            (ih (st2'.freshVar .i1).2 pk.2 _ _ hst1 hst' v (.inl k) pk.1 hinv3 hkClean hEvalK)
          rw [← hcodeEq]
          rw [evalCodeF_letBind_evalExpr rfl]
          rw [hexclEval]
          simp only []
          rw [evalCodeF_letBind_evalExpr rfl]
          dsimp only [evalExpr, evalScalarExpr]
          rw [VarEnv.bind_self]; dsimp only [evalUnaryOp]
          exact hkEval
      | _ =>
        dsimp only at h_lower hrhsEval
        split at h_lower
        · exact nomatch h_lower
        · rename_i pk hk
          injection h_lower with hp; rcases Prod.mk.inj hp with ⟨hcodeEq, _⟩
          have hkClean : lowerImpureStepPure fuel ctx st2' (.inl k) = .ok pk := hk
          have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 (venv.bind dst val) hst1 v hst'
            (ih st2' pk.2 _ (venv.bind dst val) hst1 hst' v (.inl k) pk.1 hinv2' hkClean hEvalK)
          rw [← hcodeEq]
          rw [evalCodeF_letBind_evalExpr (FuncEnv.callTarget?_of_evalExpr_ok hres hrhsEval)]
          rw [hrhsEval]
          exact hkEval

/-- Mirror of `lowerScalarSlotCtor_sound` (CtorScalarCall) with both environments. -/
theorem lowerScalarSlotCtor_soundF (Δ : DeclEnv) (Φ : FuncEnv) (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (fvarId : Lean.FVarId) (binderName : Lean.Name) (declTy : Lean.Expr)
    (info : Lean.Compiler.LCNF.CtorInfo) (args : Array (Lean.Compiler.LCNF.Arg .impure))
    (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (hsc : (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0)) = true)
    (h_lower : (do
      let some spec := ctx.findLayout? info.name
        | throw s!"[lean-native] Unknown constructor layout `{info.name}`"
      if args.size != spec.objSlots then
        throw s!"[lean-native] Ctor `{info.name}` expected {spec.objSlots} object args, got {args.size}"
      let (objVars, st1) ← lowerRealArgList ctx st true args.toList
      let objTys := objVars.map st1.getVarType
      if !(objTys.all fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t) then
        throw s!"[lean-native] Unsupported object field type in `{info.name}`"
      let (zeros, stZ) := allocZeroScalarSlotsPure st1 spec.scalarSlots
      let (dst, st2) := stZ.allocFreshFVar fvarId .objPtr
      let st2' := st2.setActiveCtor dst info.name
      let (kCode, st3) ← lowerImpureStepPure fuel ctx st2' (.inl k)
      return (wrapZeroScalarSlotsPure zeros
        (.letBind dst .objPtr (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) kCode), st3) :
        Except String (LNIRCode × RealBridgeState)) = .ok (code, st'))
    (h_eval : evalStepF Δ (fuel + 1) ctx lenv hst
      (.inl (.let { fvarId := fvarId, binderName := binderName, type := declTy,
                    value := .ctor info args himp } k)) = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
  rw [evalStepF.eq_def] at h_eval
  simp only at h_eval
  split at h_eval
  · rename_i heq
    rw [show LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget? Δ ctx
        (.ctor info args himp) = none from rfl] at heq
    exact nomatch heq
  dsimp only [evalLetValue] at h_eval
  rw [hsc] at h_eval; simp only [↓reduceIte] at h_eval
  cases hlay : ctx.findLayout? info.name <;> rw [hlay] at h_lower h_eval
  · exact nomatch h_lower
  · rename_i spec; dsimp only at h_lower h_eval
    cases har : (args.size != spec.objSlots) <;>
      simp only [har, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
    · cases hargL : lowerRealArgList ctx st true args.toList with
      | error _ => rw [hargL] at h_lower; exact nomatch h_lower
      | ok pa =>
        rw [hargL] at h_lower; rcases pa with ⟨objVars, st1⟩; dsimp only at h_lower
        rcases lowerRealArgList_sound ctx st lenv venv true args.toList objVars st1 hinv hargL with
          ⟨vs, hevalArgs, hvarList, _, hst1Eq, _⟩
        have hltVars := lowerRealArgList_lt ctx true args.toList st st1 lenv venv objVars hinv hargL
        subst st1
        rw [hevalArgs] at h_eval; dsimp only at h_eval
        cases htyOk : (!(objVars.map st.getVarType).all
            (fun t => isSupportedStage1BScalarOrTuple t ctx.arch || isHeapPtrType t)) <;>
          simp only [htyOk, ↓reduceIte, Bool.false_eq_true] at h_lower
        · rcases allocZeroScalarSlotsPure_relF Φ spec.scalarSlots st lenv venv fuel hst hinv with
            ⟨venvZ, hinvZ, hagreeZ, hvlZeros, hwrapZ⟩
          let zeros := (allocZeroScalarSlotsPure st spec.scalarSlots).1
          let stZ := (allocZeroScalarSlotsPure st spec.scalarSlots).2
          let dst := (stZ.allocFreshFVar fvarId .objPtr).1
          let st2 := (stZ.allocFreshFVar fvarId .objPtr).2
          let st2' := st2.setActiveCtor dst info.name
          have hdstEq : dst = stZ.nextVarId := rfl
          have hluDst : st2.lookupFVar? fvarId = some dst := by
            dsimp only [st2, dst]; rw [lookupFVar_allocFresh, beq_self_eq_true]; rfl
          have hobjZ : evalVarList venvZ objVars = .ok vs :=
            (evalVarList_venv_agree objVars venv venvZ st.nextVarId hltVars hagreeZ).trans hvarList
          cases hk : lowerImpureStepPure fuel ctx st2' (.inl k) with
          | error _ => rw [hk] at h_lower; exact nomatch h_lower
          | ok pk =>
            rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
            rw [hwrapZ]
            let zvals := spec.scalarSlots.map fun _ => Val.u64 0
            cases hempty : (vs.isEmpty && zvals.isEmpty)
            · dsimp only [zvals] at hempty
              rw [hempty] at h_eval; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
              cases hwf : (!vs.all Val.wfField)
              · rw [hwf] at h_eval; simp only [Bool.false_eq_true, ↓reduceIte] at h_eval
                let allocRes := hst.allocHeapCtor spec.cidx vs zvals
                have hallocEval : evalExpr venvZ hst
                    (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) =
                    .ok (.objPtr allocRes.1, allocRes.2) := by
                  dsimp only [evalExpr]; rw [hobjZ, hvlZeros]
                  change (if (vs.isEmpty && zvals.isEmpty) then _ else _) = _
                  rw [hempty, hwf]; rfl
                have hinv2 : BridgeStateInv st2
                    (lenv.bind fvarId (.objPtr allocRes.1) none (some .objPtr))
                    (venvZ.bind dst (.objPtr allocRes.1)) :=
                  bridgeInv_bind_fresh stZ lenv venvZ fvarId .objPtr (.objPtr allocRes.1) hinvZ
                have hinv2' : BridgeStateInv st2'
                    (lenv.bind fvarId (.objPtr allocRes.1) (some info.name) (some .objPtr))
                    (venvZ.bind dst (.objPtr allocRes.1)) := by
                  rw [← lenv_bind_withCtor]
                  exact bridgeInv_setActiveCtor st2 _ _ dst info.name fvarId hinv2 hluDst
                have hEvalK : evalStepF Δ fuel ctx
                    (lenv.bind fvarId (.objPtr allocRes.1) (some info.name) (some .objPtr))
                    allocRes.2 (.inl k) = .ok (v, hst') := h_eval
                have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ allocRes.2 v hst'
                  (ih st2' pk.2 _ _ allocRes.2 hst' v (.inl k) pk.1 hinv2' hk hEvalK)
                rw [evalCodeF_letBind_evalExpr rfl]
                rw [hallocEval]
                exact hkEval
              · rw [hwf] at h_eval; simp only [↓reduceIte] at h_eval; exact nomatch h_eval
            · dsimp only [zvals] at hempty
              rw [hempty] at h_eval; simp only [↓reduceIte] at h_eval
              let tupVal : Val := .tuple [.u64 spec.cidx.toUInt64]
              have hallocEval : evalExpr venvZ hst
                  (.allocCtor spec.cidx objVars (zeros.map Prod.fst)) = .ok (tupVal, hst) := by
                dsimp only [evalExpr]; rw [hobjZ, hvlZeros]
                change (if (vs.isEmpty && zvals.isEmpty) then _ else _) = _
                rw [hempty]; rfl
              have hinv2 : BridgeStateInv st2
                  (lenv.bind fvarId tupVal none (some .objPtr))
                  (venvZ.bind dst tupVal) :=
                bridgeInv_bind_fresh stZ lenv venvZ fvarId .objPtr tupVal hinvZ
              have hinv2' : BridgeStateInv st2'
                  (lenv.bind fvarId tupVal (some info.name) (some .objPtr))
                  (venvZ.bind dst tupVal) := by
                rw [← lenv_bind_withCtor]
                exact bridgeInv_setActiveCtor st2 _ _ dst info.name fvarId hinv2 hluDst
              have hEvalK : evalStepF Δ fuel ctx
                  (lenv.bind fvarId tupVal (some info.name) (some .objPtr))
                  hst (.inl k) = .ok (v, hst') := h_eval
              have hkEval := evalCodeF_fuel_mono_step Φ fuel pk.1 _ hst v hst'
                (ih st2' pk.2 _ _ hst hst' v (.inl k) pk.1 hinv2' hk hEvalK)
              rw [evalCodeF_letBind_evalExpr rfl]
              rw [hallocEval]
              exact hkEval
        · exact nomatch h_lower
    · exact nomatch h_lower

/-- Mirror of `lowerLetStep_sound` (CtorScalarCall), parameterized over the call rule:
    `hcall` carries the WHOLE obligation of the resolved-local-call arm (the one arm L1's
    semantics deliberately errors on), so this lemma stays mechanical and the L2 (and a
    later L3) instantiation supplies the alignment machinery. The 14 non-`ctor`/`fap`
    value constructors are enumerated explicitly because each supplies its own
    source-side callTarget? miss by `rfl` (`proj`/`const` are impossible at `.impure`). -/
theorem lowerLetStep_soundF (Δ : DeclEnv) (Φ : FuncEnv)
    (hres : ∀ p ∈ Φ, reservedRuntimeName p.1.name = false)
    (fuel : Nat) (ctx : RealBridgeCtx)
    (ih : ∀ (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
      (target : Lean.Compiler.LCNF.Code .impure ⊕
        (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
      (code : LNIRCode),
      BridgeStateInv st lenv venv →
      lowerImpureStepPure fuel ctx st target = .ok (code, st') →
      (match target with
       | .inl c => evalStepF Δ fuel ctx lenv hst (.inl c) = .ok (v, hst')
       | .inr (condVar, isBool, idx, discr?, alts) =>
         condVar < st.nextVarId ∧
         (∀ dx, discr? = some dx → (st.lookupFVar? dx).isSome = true) ∧
         (lnirTypeEq (st.getVarType condVar) .i1 = true → isBool = true) ∧
         ∃ cond, venv condVar = some cond ∧
           evalStepF Δ fuel ctx lenv hst (.inr (cond, isBool, idx, discr?, alts)) = .ok (v, hst')) →
      evalCodeF Φ fuel venv hst code = .ok (v, hst'))
    (st st' : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (k : Lean.Compiler.LCNF.Code .impure) (code : LNIRCode)
    (hinv : BridgeStateInv st lenv venv)
    (hcall : ∀ (fvarId : Lean.FVarId) (binderName : Lean.Name) (declTy : Lean.Expr)
      (fnName : Lean.Name) (argsA : Array (Lean.Compiler.LCNF.Arg .impure))
      (himp : Lean.Compiler.LCNF.Purity.impure = .impure) (sym : String),
      ctx.findLocalCallee? fnName = some sym →
      (do
        let (argVars, zeroBinds, st1) ← lowerCallArgsWithErasedPure ctx st argsA.toList
        let (dst, st2) := st1.allocFreshFVar fvarId (lowerGroundImpureTypeWith ctx declTy)
        let (kCode, st3) ← lowerImpureStepPure fuel ctx st2 (.inl k)
        return (wrapZeroScalarSlotsPure zeroBinds
          (.letBind dst (lowerGroundImpureTypeWith ctx declTy)
            (.call sym argVars (lowerGroundImpureTypeWith ctx declTy) false) kCode), st3) :
          Except String (LNIRCode × RealBridgeState)) = .ok (code, st') →
      evalStepF Δ (fuel + 1) ctx lenv hst
        (.inl (.let ⟨fvarId, binderName, declTy, .fap fnName argsA himp⟩ k)) = .ok (v, hst') →
      evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst'))
    (h_lower : lowerImpureStepPure (fuel + 1) ctx st (.inl (.let decl k)) = .ok (code, st'))
    (h_eval : evalStepF Δ (fuel + 1) ctx lenv hst (.inl (.let decl k)) = .ok (v, hst')) :
    evalCodeF Φ (fuel + 1) venv hst code = .ok (v, hst') := by
  dsimp only [lowerImpureStepPure] at h_lower
  rcases decl with ⟨fvarId, binderName, declTy, lv⟩
  cases hlv : lv with
  | ctor info args himp =>
    subst hlv; dsimp only at h_lower
    cases hsc : (ctx.allowStage1DHeap && (info.usize > 0 || info.ssize > 0))
    · rw [hsc] at h_lower; simp only [Bool.false_eq_true, ↓reduceIte] at h_lower
      apply lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
        ⟨fvarId, binderName, declTy, .ctor info args himp⟩ k code hinv
        (fun _ _ _ h => by cases h; exact hsc) rfl _ h_eval
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower ⊢
      cases hl : lowerImpureLetValuePure ctx st (.ctor info args himp) (lowerGroundImpureTypeWith ctx declTy)
      · rw [hl] at h_lower; exact nomatch h_lower
      · rename_i pl; rw [hl] at h_lower; dsimp only at h_lower ⊢
        have h_eval0 : evalStepF Δ (fuel + 1) ctx lenv hst
            (.inl (.let ⟨fvarId, binderName, declTy, .ctor info args himp⟩ k)) = .ok (v, hst') := h_eval
        rw [evalStepF.eq_def] at h_eval0
        simp only at h_eval0
        split at h_eval0
        · rename_i heq
          rw [show LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget? Δ ctx
              (.ctor info args himp) = none from rfl] at heq
          exact nomatch heq
        cases hev : evalLetValue ctx lenv hst (.ctor info args himp) (lowerGroundImpureTypeWith ctx declTy)
        · rw [hev] at h_eval0; exact nomatch h_eval0
        · rename_i pev
          have hnotEx : ∀ u, pl.1 ≠ .isExclusive u := by
            intro u hex
            dsimp only [lowerImpureLetValuePure] at hl
            dsimp only [evalLetValue] at hev
            rw [hsc] at hev; simp only [Bool.false_eq_true, ↓reduceIte] at hev
            rcases lowerRealCtor_sound ctx st lenv venv info.name info.cidx args.toList
                (lowerGroundImpureTypeWith ctx declTy) pl.1 pl.2 pev.1 hst pev.2.1 pev.2.2 hinv hl hev with
              ⟨_, _, hempC, hneC⟩
            cases hb : args.toList.isEmpty
            · rcases hneC hb with ⟨_, he, _⟩ | ⟨_, _, _, _, he, _⟩ <;> (rw [hex] at he; exact nomatch he)
            · rcases hempC hb with ⟨⟨_, he, _⟩, _⟩; rw [hex] at he; exact nomatch he
          rcases pl with ⟨rhs, st1⟩; dsimp only at h_lower hnotEx ⊢
          cases hrhs : rhs
          all_goals (try exact False.elim (hnotEx _ hrhs))
          all_goals (rw [hrhs] at h_lower; exact h_lower)
    · rw [hsc] at h_lower; simp only [↓reduceIte] at h_lower
      exact lowerScalarSlotCtor_soundF Δ Φ fuel ctx ih st st' lenv venv hst hst' v
        fvarId binderName declTy info args himp k code hinv hsc h_lower h_eval
  | fap fnName args himp =>
    subst hlv; dsimp only at h_lower
    cases hloc : ctx.findLocalCallee? fnName with
    | some sym =>
      rw [hloc] at h_lower; dsimp only at h_lower
      exact hcall fvarId binderName declTy fnName args himp sym hloc h_lower h_eval
    | none =>
      rw [hloc] at h_lower; dsimp only at h_lower
      have hnc_src : LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget? Δ ctx
          (.fap fnName args himp) = none := by
        simp only [LeanNative.IR.RealLCNFSemantics.DeclEnv.callTarget?]
        cases hl : LeanNative.IR.RealLCNFSemantics.DeclEnv.lookup? Δ fnName
        · rfl
        · rw [hloc]; rfl
      apply lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
        ⟨fvarId, binderName, declTy, .fap fnName args himp⟩ k code hinv
        (fun _ _ _ h => nomatch h) hnc_src _ h_eval
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower ⊢
      cases hl : lowerImpureLetValuePure ctx st (.fap fnName args himp) (lowerGroundImpureTypeWith ctx declTy)
      · rw [hl] at h_lower; exact nomatch h_lower
      · rename_i pl; rw [hl] at h_lower; dsimp only at h_lower ⊢
        have h_eval0 : evalStepF Δ (fuel + 1) ctx lenv hst
            (.inl (.let ⟨fvarId, binderName, declTy, .fap fnName args himp⟩ k)) = .ok (v, hst') := h_eval
        rw [evalStepF.eq_def] at h_eval0
        simp only at h_eval0
        split at h_eval0
        · rename_i heq
          rw [hnc_src] at heq
          exact nomatch heq
        cases hev : evalLetValue ctx lenv hst (.fap fnName args himp) (lowerGroundImpureTypeWith ctx declTy)
        · rw [hev] at h_eval0; exact nomatch h_eval0
        · rename_i pev
          have hnotEx : ∀ u, pl.1 ≠ .isExclusive u := by
            intro u hex
            have hl0 := hl
            dsimp only [lowerImpureLetValuePure, Bind.bind, Except.bind] at hl0
            cases hsl : lowerSliceCallPure? st fnName args.toList (lowerGroundImpureTypeWith ctx declTy)
                (ctx.findLocalCallee? fnName).isSome ctx.arch
            · rw [hsl] at hl0; dsimp only at hl0
              cases ha : lowerRealArgList ctx st false args.toList
              · rw [ha] at hl0; exact nomatch hl0
              · rename_i pa; rw [ha] at hl0; dsimp only at hl0
                cases hi : lowerCanonicalIntrinsicPure? fnName pa.1 (lowerGroundImpureTypeWith ctx declTy)
                    (pa.1.map pa.2.getVarType) (ctx.findLocalCallee? fnName).isSome ctx.arch ctx.gfSimdIntrinsics
                · rw [hi] at hl0; exact nomatch hl0
                · rename_i e0; rw [hi] at hl0
                  injection hl0 with hp; rcases Prod.mk.inj hp with ⟨he0, _⟩
                  rcases lowerCanonicalIntrinsicPure_sound ctx st lenv venv hst pev.2.1 fnName args himp
                      pa.1 pa.2 (lowerGroundImpureTypeWith ctx declTy) e0 pev.1 pev.2.2 hinv ha hi hev with
                    ⟨_, _, _, _, se, hse, _⟩
                  rw [he0, hex] at hse; exact nomatch hse
            · rename_i eSlice; rw [hsl] at hl0
              injection hl0 with hp; rcases Prod.mk.inj hp with ⟨heS, _⟩
              rcases lowerSliceCallPure_sound ctx st lenv venv hst pev.2.1 fnName args himp
                  (lowerGroundImpureTypeWith ctx declTy) eSlice pev.1 pev.2.2 hinv hsl hev with
                ⟨_, _, _, hdisj⟩
              rcases hdisj with ⟨_, hlen⟩ | ⟨_, _, _, hget⟩
              · rw [heS, hex] at hlen; exact nomatch hlen
              · rw [heS, hex] at hget; exact nomatch hget
          rcases pl with ⟨rhs, st1⟩; dsimp only at h_lower hnotEx ⊢
          cases hrhs : rhs
          all_goals (try exact False.elim (hnotEx _ hrhs))
          all_goals (rw [hrhs] at h_lower; exact h_lower)
  | lit a =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .lit a⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | erased =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .erased⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | proj a b c hpu => exact nomatch hpu
  | const a b c hpu => exact nomatch hpu
  | fvar a b =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .fvar a b⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | oproj a b hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .oproj a b hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | uproj a b hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .uproj a b hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | sproj a b c hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .sproj a b c hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | pap a b hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .pap a b hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | reset a b hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .reset a b hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | reuse a b c d hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .reuse a b c d hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | box a b hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .box a b hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | unbox a hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .unbox a hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval
  | isShared a hpu =>
    subst hlv
    exact lowerLetNonScalarCtor_soundF Δ Φ hres fuel ctx ih st st' lenv venv hst hst' v
      ⟨fvarId, binderName, declTy, .isShared a hpu⟩ k code hinv
      (fun _ _ _ h => by cases h) rfl h_lower h_eval

end LeanNative.Proofs
