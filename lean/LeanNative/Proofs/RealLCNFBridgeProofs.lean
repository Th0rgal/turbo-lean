import LeanNative.Proofs.RealLCNFBridge.CtorScalarCall
import LeanNative.Proofs.SymbolicTVRefinesSoundness
import LeanNative.IR.BridgeHelpers.RealBridgeCtxAndSlices

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-!
## L1 contract (roadmap/HORIZONS.md, H1 rung L1 "Single path") — w-l1

Authoritative row (`roadmap/HORIZONS.md`): "L1 Single path — The pure lowering and dead
helpers are gone. The theorem is stated for the context the driver builds, with no unproved
post-pass (each one is proved, validated by a proved checker, or removed)." Accept:
"one lowering callee; `ΔLOC < 0`".

This section is the contract-first statement of the exact signatures L1 proves in this
leaf. It is a contract section rather than `sorry` skeletons because the repo gates hold
`0 sorryAx` on every commit (Contract V5 check 2; `VALIDATION_CONTRACTS.md` V1 admits
`sorry` placeholders only during task setup, which the per-commit axiom gate here does
not). The theorems land proved, verbatim, in the follow-up commits of this same leaf.
The L2 lane (calls) builds against these names and binder shapes; L2 adds a function
environment to both semantics and restates them with that one extra binder — the names
below stay.

### New definition (driver post-pass, gated by a kernel-proved checker)

In `lean/LeanNative/IR/BridgeHelpers/RealBridgeCtxAndSlices.lean`, namespace
`LeanNative.IR`:

```
def applyValidatedCompression (d : LNIRDecl) (cand : LNIRCode) : LNIRDecl
```

Semantics: accept the (untrusted) scalar-compression candidate `cand` for `d.body` only
when the total, kernel-proved refinement checker admits it —
`LeanNative.Proofs.runSymbolicValidatedDecl` (`SymbolicTVRefinesDefs.lean`, the
Contract-V2 `VerifiedTVPassContract` gate, backed by `symbolicValidatedDeclOpt_sound`);
otherwise return `d` unchanged. On acceptance, `retTy` is recomputed from
`inferReturnedType cand` (tuple case), `assurance := AssuranceLevel.combine d.assurance
.translationValidated`, `isGpuCand` is recomputed, and `params` are never changed.
`ingestImpureDeclViaReal` replaces its inline `validateTranslationDecl`-gated compression
block with this function: the old gate is Alive2-style screening whose soundness statement
(`validateTranslationDeclSound`) speaks about symbolic summaries and sampled concrete
refinement, not `CodeRefines`; the new gate has the kernel theorem. The
`gateCodeWithSymbolicTV` screen inside the candidate producer (`compressScalarCode`)
stays — producers are untrusted proposals.

### Theorem 1 — the post-pass refines (kills the drop-the-gate mutant)

In this file, namespace `LeanNative.Proofs`:

```
theorem applyValidatedCompression_refines (d : LNIRDecl) (cand : LNIRCode) :
    (applyValidatedCompression d cand).params = d.params ∧
    CodeRefines d.body (applyValidatedCompression d cand).body
```

### Theorem 2 — the driver-shaped end-to-end statement (the L1 headline)

```
theorem lowerRealLCNFDecl_driver_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String) (cand : LNIRCode)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCode fuel
      (((applyValidatedCompression d cand).params.zip args).foldl
        (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst (applyValidatedCompression d cand).body = .ok (v, hst')
```

`ctx` is universally quantified, so the statement covers exactly the context the driver
builds (`buildRealBridgeCtxM` output — `evalRealLCNFDecl` reads the same `ctx`, which is
what ties the hypothesis to the driver's run), and `cand` is universally quantified, so it
covers every candidate the producer proposes. The object of the theorem is the emitted
declaration — base or compressed — not the pre-post-pass intermediate. The shape is
forward simulation on successful runs, as HORIZONS states the honest H1 shape.

### Removals (the other half of the rung)

1. The second, unproved lowering is deleted from `lean/LeanNative/IR/Bridge.lean`:
   `lowerPureCode`, `lowerPureAlts`, `lowerPureLetValue`, `lowerNamedCall`,
   `lowerFVarCall`, `lowerTagBranch`, `lowerImpureLetValue`, `lowerImpureCode`,
   `ingestLCNFDeclGenericWithState`, `ingestLCNFDeclGeneric`, `ingestLCNFMonoDecl`.
   A declaration with no impure LCNF form is `Unsupported` on the proved path:
   `ingestModuleDeclsWith` drops its mono arm (the `ingestMono` parameter leaves its
   signature) and such declarations are left to the stock backend.
2. Helpers that this deletion strands (the `lowerPureCode`-only cascade and the
   already-dead set the roadmap counted at about 250 LOC) are deleted in this leaf; the
   name inventory in `lean/LeanNative/Tests/BridgeHelpersSplitPin.lean` is updated in the
   same commit as each deletion, with zero-reference evidence in the commit message.
3. The axiom audit keeps `lowerRealLCNFCode_sound` / `lowerRealLCNFDecl_sound` in its
   required set; the two theorems above are added to
   `lean/LeanNative/Proofs/AxiomAudit.lean`'s audited list.

### Named exclusions (recorded, not silently kept)

- `tryLowerGfSimdIntrinsic` — a named intrinsic substitution keyed on the declaration
  name; it inspects no `Code`, so it is not an LCNF lowering, and it sits outside the
  proved single path with `assurance := .tested`. Gating or removing it is H3 plugin work
  (HORIZONS: accelerator plugins last).
- `normalizeEmbeddedSliceGetBang` — the "LCNF rewrite" the H1 review found; it runs only
  under `TargetArch.isFreestandingEmbedded`, the unverified non-LLVM tier (HORIZONS H1
  rule: unverified backends get no features until H3). On the proved path the lowerer
  receives the driver's LCNF unchanged.

### Acceptance (quoted) and gates

- "one lowering callee": after the removals, `lowerRealLCNFDecl` (via
  `lowerRealLCNFCode` / `lowerImpureStepPure`) is the only `LCNF → LNIR` lowering callee
  in the tree.
- "`ΔLOC < 0`" over the leaf.
- Gates: `(cd lean && lake build TurboLean LeanNative)`;
  `turbo-lean --json audit-spec lean/TurboLean/Spec.lean` (98/98) and
  `lean/LeanNative/Spec.lean` (124/124);
  `turbo-lean --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/
  lean/LeanNative/Transform/ lean/TurboLean/ConLeche.lean lean/TurboLean/ElabAudit.lean`
  (ok; 0 vacuous, 0 trivial, 0 stub_defs, 0 forbidden_scope_decls);
  `python3 scripts/sync_docs_inventory.py --check`. Executable mutant-kill guards for the
  gate land in `lean/LeanNative/Tests/RealLCNFBridgeTests.lean`: a wrong-value candidate
  is rejected, an equivalent candidate is accepted with `.translationValidated`, an
  ill-typed candidate is rejected.
-/

private theorem lowerImpureStepPure_sound_aux (fuel : Nat) (ctx : RealBridgeCtx) :
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
      evalCode fuel venv hst code = .ok (v, hst') := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; exact nomatch h
  | succ fuel ih =>
    intro st st' lenv venv hst hst' v target code hinv h_lower h_side
    cases target with
    | inr t =>
      rcases t with ⟨condVar, isBool, idx, discr?, alts⟩
      rcases h_side with ⟨hcondLt, hdiscr, hi1, cond, hcondV, h_eval⟩
      exact lowerStepInr_sound fuel ctx ih st st' lenv venv hst hst' v
        condVar isBool idx discr? alts code cond hinv h_lower hcondLt hdiscr hi1 hcondV h_eval
    | inl c =>
      have h_eval : evalStep (fuel + 1) ctx lenv hst (.inl c) = .ok (v, hst') := h_side
      cases c with
      | «let» decl k =>
        exact lowerLetStep_sound fuel ctx ih st st' lenv venv hst hst' v decl k code hinv h_lower h_eval
      | setTag x cidx k himp =>
        exact lowerSetTag_sound fuel ctx ih st st' lenv venv hst hst' v x cidx k himp code hinv h_lower h_eval
      | «return» x =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, _, _⟩
          rw [hvalL] at h_eval; injection h_eval with hpv; rcases Prod.mk.inj hpv with ⟨rfl, rfl⟩
          dsimp only [evalCode]; rw [hvalV]
      | unreach _ => dsimp only [evalStep] at h_eval; exact nomatch h_eval
      | «fun» _ _ _ => dsimp only [evalStep] at h_eval; exact nomatch h_eval
      | inc x n _ _ k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          cases hrc : applyRc true lenv hst x n with
          | error _ => rw [hrc] at h_eval; exact nomatch h_eval
          | ok hst1 =>
            rw [hrc] at h_eval
            cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure true vid (st.getVarType vid) n pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                exact lowerRefOpPure_sound (fuel + 1) true vid (st.getVarType vid) n pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
      | dec x n _ _ _ k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i vid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x vid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          cases hrc : applyRc false lenv hst x n with
          | error _ => rw [hrc] at h_eval; exact nomatch h_eval
          | ok hst1 =>
            rw [hrc] at h_eval
            cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure false vid (st.getVarType vid) n pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                exact lowerRefOpPure_sound (fuel + 1) false vid (st.getVarType vid) n pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval))
      | del x k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, _, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          rw [hvalL, hisHeap] at h_eval
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
          · cases hk : lowerImpureStepPure fuel ctx st (.inl k) with
            | error _ => rw [hk] at h_lower; exact nomatch h_lower
            | ok pk =>
              rw [hk] at h_lower; dsimp only at h_lower
              cases hrop : lowerRefOpPure false objVid (st.getVarType objVid) 1 pk.1 <;> rw [hrop] at h_lower
              · exact nomatch h_lower
              · injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                have hrcEq : ∃ hst1, applyRc false lenv hst x 1 = .ok hst1 ∧
                    evalStep fuel ctx lenv hst1 (.inl k) = .ok (v, hst') := by
                  unfold applyRc; rw [hisHeap, hvalL]
                  cases hih : isHeapPtrType (st.getVarType objVid) <;>
                    simp only [hih, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h_eval ⊢
                  · cases val <;> exact ⟨hst, rfl, h_eval⟩
                  · cases val with
                    | objPtr objId =>
                      dsimp only at h_eval ⊢
                      cases hd : hst.decRefObj objId 1 with
                      | error _ => rw [hd] at h_eval; exact nomatch h_eval
                      | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                    | sarrayId bufId =>
                      dsimp only at h_eval ⊢
                      cases hd : hst.decRefBuf bufId 1 with
                      | error _ => rw [hd] at h_eval; exact nomatch h_eval
                      | ok hst1 => rw [hd] at h_eval; exact ⟨hst1, rfl, h_eval⟩
                    | _ => exact ⟨hst, rfl, h_eval⟩
                rcases hrcEq with ⟨hst1, hrc, h_eval1⟩
                exact lowerRefOpPure_sound (fuel + 1) false objVid (st.getVarType objVid) 1 pk.1 _ lenv venv hst hst1 hst'
                  x val v htyL hvalL hvalV hrop hrc
                  (evalCode_fuel_mono_step fuel pk.1 venv hst1 v hst' (ih st pk.2 lenv venv hst1 hst' v (.inl k) pk.1 hinv hk h_eval1))
          · cases val with
            | objPtr objId =>
              dsimp only at h_eval
              cases hdel : hst.delObjShell objId with
              | error _ => rw [hdel] at h_eval; exact nomatch h_eval
              | ok hst1 =>
                rw [hdel] at h_eval
                cases hk : lowerImpureStepPure fuel ctx (st.freshVar .unit).2 (.inl k) with
                | error _ => rw [hk] at h_lower; exact nomatch h_lower
                | ok pk =>
                  rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                  have hinv2 := bridgeInv_freshVar st lenv venv .unit .unit hinv
                  have hkEval := evalCode_fuel_mono_step fuel pk.1 _ hst1 v hst'
                    (ih (st.freshVar .unit).2 pk.2 lenv _ hst1 hst' v (.inl k) pk.1 hinv2 hk h_eval)
                  have hcall : evalExpr venv hst (.call "lean_native_del_obj" [objVid] .unit false) = .ok (.unit, hst1) := by
                    unfold evalExpr; dsimp only [evalVarList]
                    rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                    rw [hdel]; rfl
                  dsimp only [evalCode]; rw [hcall]; exact hkEval
            | _ => exact nomatch h_eval
      | oset x idx y k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar x = isHeapPtrType (st.getVarType objVid) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          cases hhp : (ctx.allowStage1DHeap && isHeapPtrType (st.getVarType objVid)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower
          · cases hunb : isUnboxedScalarOrTuple (st.getVarType objVid) <;>
              simp only [hunb, ↓reduceIte, Bool.false_eq_true] at h_lower
            · exact nomatch h_lower
            · rw [hisHeap, unboxed_not_heap _ hunb] at h_eval
              simp only [Bool.not_false, ↓reduceIte] at h_eval
              exact evalCode_fuel_mono_step fuel code venv hst v hst'
                (ih st st' lenv venv hst hst' v (.inl k) code hinv h_lower h_eval)
          · have hhp2 : isHeapPtrType (st.getVarType objVid) = true := (Bool.and_eq_true _ _).mp hhp |>.2
            rw [hisHeap, hhp2, hvalL] at h_eval
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_eval
            cases hy : lowerRealArg ctx st y true with
            | error _ => rw [hy] at h_lower; exact nomatch h_lower
            | ok py =>
              rw [hy] at h_lower; rcases py with ⟨valVid, stY⟩
              rcases lowerRealArg_sound ctx st lenv venv y true valVid stY hinv hy with
                ⟨yx, yVal, rfl, hluY, hevalY, hyValV, _, hstY⟩
              subst stY; dsimp only at h_lower
              have hvalLt : valVid < st.nextVarId := hinv.fvar_lt yx valVid hluY
              cases val with
              | objPtr objId =>
                dsimp only at h_eval; rw [hevalY] at h_eval; dsimp only at h_eval
                cases hwf : writeField hst objId (idx.toUInt64).toNat yVal true with
                | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                | ok hst1 =>
                  rw [hwf] at h_eval
                  let st3 := (st.freshVar .i64).2
                  let st4 := (st3.freshVar .unit).2
                  cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                  | error _ => rw [hk] at h_lower; exact nomatch h_lower
                  | ok pk =>
                    rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                    let venv1 := venv.bind (st.freshVar .i64).1 (.u64 idx.toUInt64)
                    let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                    have hinv4 : BridgeStateInv st4 lenv venv2 :=
                      bridgeInv_freshVar st3 lenv venv1 .unit .unit
                        (bridgeInv_freshVar st lenv venv .i64 (.u64 idx.toUInt64) hinv)
                    have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                      (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                    exact evalCtorWriteStep_sound fuel st venv hst hst1 hst' v objVid valVid objId
                      idx yVal true pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
              | _ => rw [hevalY] at h_eval; exact nomatch h_eval
      | uset x i y k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
          have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
            dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
          split at h_lower
          · exact nomatch h_lower
          · cases hc : st.resolveHeapCtor? ctx objVid x <;> rw [hc] at h_lower
            · exact nomatch h_lower
            · rename_i cname; dsimp only at h_lower
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
              · exact nomatch h_lower
              · rename_i spec; dsimp only at h_lower
                cases hsl : spec.usizeSlot? i <;> rw [hsl] at h_lower
                · exact nomatch h_lower
                · rename_i slp; rcases slp with ⟨slot, slotTy⟩; dsimp only at h_lower
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                  · exact nomatch h_lower
                  · rename_i valVid; dsimp only at h_lower
                    rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                    rw [hvalL, hyValL] at h_eval
                    cases val with
                    | objPtr objId =>
                      have hslEq : (lenv.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.usizeSlot? i)) = some (slot, slotTy) := by
                        rw [hresEq, hc]; dsimp only [Bind.bind, Option.bind]
                        rw [hlay]; dsimp only; exact hsl
                      dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                      cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                      | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                      | ok hst1 =>
                        rw [hwf] at h_eval
                        let st3 := (st.freshVar .i64).2
                        let st4 := (st3.freshVar .unit).2
                        cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                        | error _ => rw [hk] at h_lower; exact nomatch h_lower
                        | ok pk =>
                          rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                          let venv1 := venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)
                          let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                          have hinv4 : BridgeStateInv st4 lenv venv2 :=
                            bridgeInv_freshVar st3 lenv venv1 .unit .unit
                              (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                          have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                            (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                          exact evalCtorWriteStep_sound fuel st venv hst hst1 hst' v objVid valVid objId
                            slot yVal false pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
                    | _ => exact nomatch h_eval
      | sset x n off y _ k _ =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar x <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i objVid; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv x objVid hinv hv with ⟨_, hobjLt, ⟨val, hvalL, hvalV⟩, _, hctorL⟩
          have hresEq : lenv.resolveCtor? ctx x = st.resolveHeapCtor? ctx objVid x := by
            dsimp [LEnv.resolveCtor?, RealBridgeState.resolveHeapCtor?]; rw [hctorL]
          split at h_lower
          · exact nomatch h_lower
          · cases hc : st.resolveHeapCtor? ctx objVid x <;> rw [hc] at h_lower
            · exact nomatch h_lower
            · rename_i cname; dsimp only at h_lower
              cases hlay : ctx.findLayout? cname <;> rw [hlay] at h_lower
              · exact nomatch h_lower
              · rename_i spec; dsimp only at h_lower
                cases hsl : spec.scalarSlot? n off <;> rw [hsl] at h_lower
                · exact nomatch h_lower
                · rename_i slp; rcases slp with ⟨slot, sfTy⟩; dsimp only at h_lower
                  cases hy : st.lookupBoundFVar y <;> rw [hy] at h_lower
                  · exact nomatch h_lower
                  · rename_i valVid; dsimp only at h_lower
                    rcases lookupBoundFVar_inv st lenv venv y valVid hinv hy with ⟨_, hvalLt, ⟨yVal, hyValL, hyValV⟩, _, _⟩
                    rw [hvalL, hyValL] at h_eval
                    cases val with
                    | objPtr objId =>
                      have hslEq : (lenv.resolveCtor? ctx x >>= ctx.findLayout? >>= (·.scalarSlot? n off)) = some (slot, sfTy) := by
                        rw [hresEq, hc]; dsimp only [Bind.bind, Option.bind]
                        rw [hlay]; dsimp only; exact hsl
                      dsimp only at h_eval; rw [hslEq] at h_eval; dsimp only at h_eval
                      cases hwf : writeField hst objId (slot.toUInt64).toNat yVal false with
                      | error _ => rw [hwf] at h_eval; exact nomatch h_eval
                      | ok hst1 =>
                        rw [hwf] at h_eval
                        let st3 := (st.freshVar .i64).2
                        let st4 := (st3.freshVar .unit).2
                        cases hk : lowerImpureStepPure fuel ctx st4 (.inl k) with
                        | error _ => rw [hk] at h_lower; exact nomatch h_lower
                        | ok pk =>
                          rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                          let venv1 := venv.bind (st.freshVar .i64).1 (.u64 slot.toUInt64)
                          let venv2 := venv1.bind (st3.freshVar .unit).1 .unit
                          have hinv4 : BridgeStateInv st4 lenv venv2 :=
                            bridgeInv_freshVar st3 lenv venv1 .unit .unit
                              (bridgeInv_freshVar st lenv venv .i64 (.u64 slot.toUInt64) hinv)
                          have hkEval := evalCode_fuel_mono_step fuel pk.1 venv2 hst1 v hst'
                            (ih st4 pk.2 lenv venv2 hst1 hst' v (.inl k) pk.1 hinv4 hk h_eval)
                          exact evalCtorWriteStep_sound fuel st venv hst hst1 hst' v objVid valVid objId
                            slot yVal false pk.1 hobjLt hvalLt hvalV hyValV hwf hkEval
                    | _ => exact nomatch h_eval
      | cases cs =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hv : st.lookupBoundFVar cs.discr <;> rw [hv] at h_lower
        · exact nomatch h_lower
        · rename_i condVar; dsimp only at h_lower
          rcases lookupBoundFVar_inv st lenv venv cs.discr condVar hinv hv with
            ⟨hluC, hcondLt, ⟨discrVal, hvalL, hvalV⟩, htyL, _⟩
          have hisHeap : lenv.isHeapVar cs.discr = isHeapPtrType (st.getVarType condVar) := by
            dsimp only [LEnv.isHeapVar]; rw [htyL]
          rw [hvalL, hisHeap] at h_eval; dsimp only at h_eval
          cases hhp : ((ctx.allowStage1DHeap || cs.typeName == ``Bool) && isHeapPtrType (st.getVarType condVar)) <;>
            simp only [hhp, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
          · cases hsc : (!isSupportedStage1BScalarType (st.getVarType condVar) ctx.arch) <;>
              simp only [hsc, ↓reduceIte, Bool.false_eq_true] at h_lower
            · rw [htyL] at h_eval; dsimp only [Option.getD] at h_eval
              have hsideSc : condVar < st.nextVarId ∧
                  (∀ dx, (none : Option Lean.FVarId) = some dx → (st.lookupFVar? dx).isSome = true) ∧
                  (lnirTypeEq (st.getVarType condVar) .i1 = true →
                    (cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1) = true) ∧
                  ∃ cond, venv condVar = some cond ∧
                    evalStep fuel ctx lenv hst
                      (.inr (cond, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none,
                        orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                refine ⟨hcondLt, ?_, ?_, discrVal, hvalV, h_eval⟩
                · intro _ h; cases h
                · intro hi1; rw [hi1, Bool.or_true]
              exact evalCode_fuel_mono_step fuel code venv hst v hst'
                (ih st st' lenv venv hst hst' v
                  (.inr (condVar, cs.typeName == ``Bool || lnirTypeEq (st.getVarType condVar) .i1, 0, none, orderAltsPure cs.alts.toList))
                  code hinv h_lower hsideSc)
            · exact nomatch h_lower
          · cases htag : tagOf discrVal hst with
            | error _ => rw [htag] at h_eval; exact nomatch h_eval
            | ok tag =>
              rw [htag] at h_eval
              rcases freshVar_spec st .i64 with ⟨htagId, hfn2, hft2, hflu2, _, _⟩
              cases hk : lowerImpureStepPure fuel ctx (st.freshVar .i64).2
                  (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) with
              | error _ => rw [hk] at h_lower; exact nomatch h_lower
              | ok pk =>
                rw [hk] at h_lower; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
                have hinv2 : BridgeStateInv (st.freshVar .i64).2 lenv (venv.bind (st.freshVar .i64).1 tag) :=
                  bridgeInv_freshVar st lenv venv .i64 tag hinv
                have hsideHp : (st.freshVar .i64).1 < (st.freshVar .i64).2.nextVarId ∧
                    (∀ dx, some cs.discr = some dx → ((st.freshVar .i64).2.lookupFVar? dx).isSome = true) ∧
                    (lnirTypeEq ((st.freshVar .i64).2.getVarType (st.freshVar .i64).1) .i1 = true → false = true) ∧
                    ∃ cond, (venv.bind (st.freshVar .i64).1 tag) (st.freshVar .i64).1 = some cond ∧
                      evalStep fuel ctx lenv hst
                        (.inr (cond, false, 0, some cs.discr, orderAltsPure cs.alts.toList)) = .ok (v, hst') := by
                  refine ⟨?_, ?_, ?_, tag, VarEnv.bind_self _ _ _, h_eval⟩
                  · rw [htagId, hfn2]; exact Nat.lt_succ_self _
                  · intro dx hdx
                    injection hdx with hd; subst dx
                    rw [hflu2, hluC]; rfl
                  · intro hi1
                    simp only [htagId, hft2 st.nextVarId, beq_self_eq_true, ↓reduceIte, lnirTypeEq, lnirTypeEqFuel] at hi1
                    exact hi1
                have hkEval := evalCode_fuel_mono_step fuel pk.1 (venv.bind (st.freshVar .i64).1 tag) hst v hst'
                  (ih (st.freshVar .i64).2 pk.2 lenv (venv.bind (st.freshVar .i64).1 tag) hst hst' v
                    (.inr ((st.freshVar .i64).1, false, 0, some cs.discr, orderAltsPure cs.alts.toList))
                    pk.1 hinv2 hk hsideHp)
                have hcall : evalExpr venv hst (.call "lean_native_ctor_tag" [condVar] .i64 false) = .ok (tag, hst) := by
                  unfold evalExpr; dsimp only [evalVarList]
                  rw [hvalV]; dsimp only [↓reduceIte, Bool.false_eq_true]
                  unfold tagOf at htag
                  cases discrVal with
                  | objPtr objId =>
                    dsimp only [Functor.map, Except.map] at htag ⊢
                    cases hl : hst.liveHeapObj objId with
                    | error _ => rw [hl] at htag; exact nomatch htag
                    | ok o =>
                      rw [hl] at htag; injection htag with ht
                      subst tag; rfl
                  | u64 n => injection htag with ht; subst tag; rfl
                  | bool b => injection htag with ht; subst tag; rfl
                  | tuple vs =>
                    cases vs with
                    | nil => exact nomatch htag
                    | cons v0 rest =>
                      cases v0 with
                      | u64 n => injection htag with ht; subst tag; rfl
                      | _ => exact nomatch htag
                  | _ => exact nomatch htag
                dsimp only [evalCode]; rw [hcall]; exact hkEval
      | jp decl k =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        cases hrec : hasJmpToPure fuel decl.fvarId (.inl decl.value) <;>
          simp only [hrec, ↓reduceIte, Bool.false_eq_true] at h_lower h_eval
        · exact evalCode_fuel_mono_step fuel code venv hst v hst'
            (ih (st.setJpDecl decl.fvarId decl.params.toList decl.value) st'
              (lenv.bindJp decl.fvarId { params := decl.params.toList, code := decl.value })
              venv hst hst' v (.inl k) code
              (bridgeInv_setJp st lenv venv decl.fvarId decl.params.toList decl.value hinv) h_lower h_eval)
        · exact nomatch h_lower
      | jmp fvarId args =>
        dsimp only [lowerImpureStepPure] at h_lower
        dsimp only [evalStep] at h_eval
        dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExcept.throw, MonadExceptOf.throw, throwThe] at h_lower
        cases hjp : st.lookupJp? fvarId <;> rw [hjp] at h_lower
        · exact nomatch h_lower
        · rename_i jpPair; rcases jpPair with ⟨jpParams, jpBody⟩; dsimp only at h_lower
          rw [hinv.jp_sync fvarId jpParams jpBody hjp] at h_eval; dsimp only at h_eval
          cases hb : bindJpCallArgsPure ctx st jpParams args.toList with
          | error _ => rw [hb] at h_lower; exact nomatch h_lower
          | ok pb =>
            rw [hb] at h_lower; rcases pb with ⟨binds, st1⟩; dsimp only at h_lower
            rcases bindJpCallArgsPure_rel ctx venv st.nextVarId jpParams args.toList st st1 lenv binds
                (Nat.le_refl _) (fun y vid hy => hinv.fvar_lt y vid hy) hinv hb with
              ⟨vs, hevalArgs, hfm1, hac1, hjp1, hnext1, hty1, hstepJp⟩
            rw [hevalArgs] at h_eval; dsimp only at h_eval
            have hinvSt1 : BridgeStateInv st1 lenv venv :=
              bridgeInv_ext st st1 lenv venv hinv hnext1 hty1 hfm1
                (fun u _ => by simp only [RealBridgeState.getActiveCtor?, hac1]) hjp1
            have hst1Lt : ∀ x vid, st1.lookupFVar? x = some vid → vid < st.nextVarId := by
              intro x vid hx
              have hx' : st.lookupFVar? x = some vid := by simp only [RealBridgeState.lookupFVar?, hfm1] at hx; exact hx
              exact hinv.fvar_lt x vid hx'
            rcases hstepJp st1 lenv venv st.nextVarId (fuel + 1) hst
                (match lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
                 | .ok (bc, _) => bc | .error _ => .unreachable)
                hinvSt1 (Nat.le_refl _) (Nat.le_refl _) rfl hst1Lt (fun _ _ => rfl) with
              ⟨lenv', venv', hbindP, hinvIn, hevalWrap⟩
            rw [hbindP] at h_eval; dsimp only at h_eval
            cases hbody : lowerImpureStepPure fuel ctx (applyJpParamMapPure st1 binds) (.inl jpBody) with
            | error _ => rw [hbody] at h_lower; exact nomatch h_lower
            | ok pbody =>
              rw [hbody] at h_lower hevalWrap; injection h_lower with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩
              rw [hevalWrap]
              exact evalCode_fuel_mono_step fuel pbody.1 venv' hst v hst'
                (ih (applyJpParamMapPure st1 binds) pbody.2 lenv' venv' hst hst' v (.inl jpBody) pbody.1 hinvIn hbody h_eval)

theorem lowerImpureStepPure_sound (fuel : Nat) (ctx : RealBridgeCtx) (st st' : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (target : Lean.Compiler.LCNF.Code .impure ⊕
      (VarId × Bool × Nat × Option Lean.FVarId × List (Lean.Compiler.LCNF.Alt .impure)))
    (code : LNIRCode) :
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
    evalCode fuel venv hst code = .ok (v, hst') :=
  lowerImpureStepPure_sound_aux fuel ctx st st' lenv venv hst hst' v target code

theorem lowerRealLCNFCode_sound (fuel : Nat) (ctx : RealBridgeCtx) (st : RealBridgeState)
    (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState) (v : Val)
    (code : Lean.Compiler.LCNF.Code .impure) (lnir : LNIRCode) (st' : RealBridgeState)
    (hinv : BridgeStateInv st lenv venv)
    (h_lower : lowerRealLCNFCode fuel ctx st code = .ok (lnir, st'))
    (h_eval : evalRealLCNFCode fuel ctx lenv hst code = .ok (v, hst')) :
    evalCode fuel venv hst lnir = .ok (v, hst') :=
  lowerImpureStepPure_sound fuel ctx st st' lenv venv hst hst' v (.inl code) lnir hinv h_lower h_eval

theorem lowerRealLCNFDecl_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState) (v : Val)
    (d : LNIRDecl) (mangled : String)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCode fuel ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) hst d.body =
      .ok (v, hst') := by
  unfold lowerRealLCNFDecl at h_lower; unfold evalRealLCNFDecl at h_eval
  cases hdv : decl.value with
  | extern _ => rw [hdv] at h_eval; exact nomatch h_eval
  | code c =>
    rw [hdv] at h_lower h_eval
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_lower h_eval
    cases hbp : bindParams ctx true LEnv.empty decl.params.toList args with
    | error _ => rw [hbp] at h_eval; exact nomatch h_eval
    | ok lenv =>
      rw [hbp] at h_eval
      cases hlc : lowerRealLCNFCode fuel ctx (internRealParams ctx {} decl.params.toList).2 c with
      | error _ => rw [hlc] at h_lower; exact nomatch h_lower
      | ok plc =>
        rw [hlc] at h_lower; injection h_lower with hd
        subst d; dsimp only
        exact lowerRealLCNFCode_sound fuel ctx (internRealParams ctx {} decl.params.toList).2 lenv _
          hst hst' v c plc.1 plc.2
          (internRealParams_sound ctx decl.params.toList args {} LEnv.empty lenv VarEnv.empty bridgeInv_empty hbp)
          hlc h_eval


private theorem runSymbolicValidatedDecl_some_eq (propose : LNIRDecl → LNIRDecl)
    (d d' : LNIRDecl) (h : runSymbolicValidatedDecl propose d = some d') :
    d' = propose d := by
  unfold runSymbolicValidatedDecl at h
  dsimp only at h
  cases hgate : (d.checkElemTypes.isNone && (propose d).checkElemTypes.isNone &&
      symbolicCodeRefines d.body (propose d).body)
  · rw [hgate] at h; cases h
  · rw [hgate] at h
    simp only [↓reduceIte, Option.some.injEq] at h
    exact h.symm

/-- L1 (`roadmap/HORIZONS.md` rung L1): the driver post-pass never changes the parameter
    list, and its output body refines the proved lowering's body — a compression candidate
    is taken only through the kernel-proved `runSymbolicValidatedDecl` gate. -/
theorem applyValidatedCompression_refines (d : LNIRDecl) (cand : LNIRCode) :
    (applyValidatedCompression d cand).params = d.params ∧
    CodeRefines d.body (applyValidatedCompression d cand).body := by
  unfold LeanNative.IR.applyValidatedCompression
  split
  · exact ⟨rfl, CodeRefines.refl d.body⟩
  · split
    next d' hrun =>
      have he := runSymbolicValidatedDecl_some_eq _ d d' hrun
      subst he
      exact ⟨rfl, symbolicValidatedDeclOpt_sound _ d _ hrun⟩
    next => exact ⟨rfl, CodeRefines.refl d.body⟩

/-- L1 headline (`roadmap/HORIZONS.md` rung L1): soundness of the lowering pipeline the
    driver runs — `lowerRealLCNFDecl` composed with the checker-gated compression post-pass
    (`applyValidatedCompression`) — stated for every context the driver builds
    (`evalRealLCNFDecl` reads the same `ctx`) and every candidate the producer proposes.
    Forward simulation on successful runs. -/
theorem lowerRealLCNFDecl_driver_sound (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState)
    (v : Val) (d : LNIRDecl) (mangled : String) (cand : LNIRCode)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCode fuel
      (((applyValidatedCompression d cand).params.zip args).foldl
        (fun acc (p, val) => acc.bind p.id val) VarEnv.empty)
      hst (applyValidatedCompression d cand).body = .ok (v, hst') := by
  obtain ⟨hp, href⟩ := applyValidatedCompression_refines d cand
  rw [hp]
  exact href fuel _ hst v hst'
    (lowerRealLCNFDecl_sound fuel ctx decl args hst hst' v d mangled h_lower h_eval)

end LeanNative.Proofs
