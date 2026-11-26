import LeanNative.Proofs.RealLCNFBridge.StepCases
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

end LeanNative.Proofs
