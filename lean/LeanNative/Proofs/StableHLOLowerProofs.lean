import LeanNative.Proofs.StableHLOCodeProofs

/-!
# Top-Level `LNIR → StableHLOAst` Soundness & Mutant Kills (`LeanNative.Proofs.StableHLOLowerProofs`)

Proves:
1. `lowerToStableHLO_sound`: end-to-end semantic preservation from `LNIRDecl`
   (`LeanNative.Semantics.evalCode`) to `StableHLOAst.FuncOp` (`StableHLOAst.evalFuncOp`)
   across both scalar/branching programs and data-parallel 1-D tensor pipelines.
2. `lowerToStableHLO_scalar_nonvacuous` & `lowerToStableHLO_pipeline_nonvacuous`:
   mechanized end-to-end non-vacuity witnesses exercising scalar `ite` diamonds (`select`)
   and a chained `sarrayLen → saxpy → dotProduct → sarrayGet` tensor pipeline.
3. `hlo_mutant_h1_killed`, `hlo_mutant_h2_killed`, `hlo_mutant_h3_killed`:
   mechanized emitter mutant-kill proofs against `hloMutantSubSwap`, `hloMutantUnmaskedShl`,
   and `hloMutantUnguardedDiv`.
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.LLVMLower (sameScalarTy)

/-! ## 1. Return-Type Simulation & Top-Level `lowerToStableHLO_sound` -/

/-- Source-to-target return-value relation determined solely by `d.retTy`. -/
def HLOReturnRel (retTy : LNIRType) (st' : HeapState) (retVal : Val) (tv : TensorVal) : Prop :=
  match retTy with
  | .sarray .i64 =>
    ∃ bufId buf,
      retVal = .sarrayId bufId ∧
      st'.findBuffer bufId = some buf ∧
      tv = mkVecUi64 buf.data
  | ty =>
    ∃ w, encodeScalarTyped ty retVal = some w ∧ tv = mkScUi64 w

theorem matchReturnKind_rel (retTy : LNIRType) (vk : HLOVarKind) (resTy : TensorType)
    (st' : HeapState) (retVal : Val) (tv : TensorVal)
    (hMatch : matchReturnKind retTy vk = some resTy)
    (hRel : HLOValRel st' vk retVal tv) :
    HLOReturnRel retTy st' retVal tv ∧ tv.ty = resTy := by
  cases vk with
  | scalar ty kn =>
    dsimp [matchReturnKind] at hMatch
    by_cases hs : sameScalarTy ty retTy = true
    · simp only [hs, ↓reduceIte, Option.some.injEq] at hMatch
      subst hMatch
      rcases sameScalarTy_eq_true ty retTy hs with ⟨heq, hor⟩
      subst heq
      rcases hRel with ⟨⟨w, hEnc, rfl⟩, _⟩
      rcases hor with h64 | h1
      · subst h64
        exact ⟨⟨w, hEnc, rfl⟩, rfl⟩
      · subst h1
        exact ⟨⟨w, hEnc, rfl⟩, rfl⟩
    · simp [hs] at hMatch
  | tensor1D n =>
    cases retTy <;> try (simp [matchReturnKind] at hMatch; done)
    case sarray elemTy =>
      cases elemTy <;> try (simp [matchReturnKind] at hMatch; done)
      simp only [matchReturnKind, Option.some.injEq] at hMatch
      subst hMatch
      rcases hRel with ⟨bid, buf, rfl, _, hFind, hSz, rfl⟩
      exact ⟨⟨bid, buf, rfl, hFind, rfl⟩, by simp [mkVecUi64, hSz]⟩

theorem list_getLast?_snoc (op : StableHLOOp) :
    (ops : List StableHLOOp) → (ops ++ [op]).getLast? = some op
  | [] => rfl
  | _ :: [] => rfl
  | _ :: b :: rest => by
    simp only [List.cons_append, List.getLast?_cons_cons]
    exact list_getLast?_snoc op (b :: rest)

/-- End-to-end lowering soundness for `StableHLOLower.lowerToStableHLO`:
if `lowerToStableHLO d tensorLen = some fn`, the arguments satisfy `HLOArgsRel`,
and source `evalCode` evaluates `d.body` to `(retVal, st')`, then `evalFuncOp fn targs`
evaluates without error to `tv` matching `fn.result` and `HLOReturnRel d.retTy st' retVal tv`. -/
theorem lowerToStableHLO_sound
    (d : LNIRDecl) (tensorLen fuel : Nat) (fn : FuncOp)
    (argVals : List Val) (targs : List TensorVal)
    (st st' : HeapState) (retVal : Val)
    (hLower : lowerToStableHLO d tensorLen = some fn)
    (hArgs : HLOArgsRel tensorLen st d.params argVals targs)
    (hEval : evalCode fuel (bindHLOParamEnv VarEnv.empty d.params argVals) st d.body =
      .ok (retVal, st')) :
    ∃ tv,
      HLOReturnRel d.retTy st' retVal tv ∧
      tv.ty = fn.result ∧
      evalFuncOp fn targs = .ok tv := by
  dsimp [lowerToStableHLO] at hLower
  cases hInit : initHLOParams tensorLen d.params with
  | none => simp [hInit] at hLower
  | some out =>
    rcases out with ⟨Γ0, params⟩
    simp only [hInit, Option.bind] at hLower
    cases hLow : lowerCode Γ0 d.body 0 with
    | none => simp [hLow] at hLower
    | some rc =>
      simp only [hLow] at hLower
      cases hMatch : matchReturnKind d.retTy rc.outKind with
      | none => simp [hMatch] at hLower
      | some resTy =>
        simp only [hMatch, Option.some.injEq] at hLower
        subst hLower
        rcases bindHLOParams_post tensorLen HLOTyEnv.empty VarEnv.empty st Env.empty
            d.params argVals targs (Γ0, params)
            (fun _ _ _ h => nomatch h)
            (fun _ _ _ h => nomatch h)
            (fun _ _ => rfl)
            hInit hArgs with
          ⟨hlen, tenv0, hBind, hAg0, hFr0⟩
        rcases lowerHLOCode_post Γ0 fuel (bindHLOParamEnv VarEnv.empty d.params argVals)
            st st' d.body retVal tenv0 0 rc hAg0 hFr0 hLow hEval with
          ⟨_, hAll, _, tv, tenv', hRel, hEx, hLook, _, _⟩
        rcases matchReturnKind_rel d.retTy rc.outKind resTy st' retVal tv hMatch hRel with
          ⟨hRetRel, hTvTy⟩
        have hLookup := lookup_of_hloValRel st' tenv' rc.reg rc.outKind retVal tv hRel hLook
        refine ⟨tv, hRetRel, hTvTy, ?_⟩
        unfold evalFuncOp
        have hlenBne : (targs.length != params.length) = false := by simp [hlen]
        rw [hlenBne]
        simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, hBind]
        rw [evalOps_append_nonReturn rc.ops [.returnOp rc.reg] tenv0 tenv' hAll hEx]
        have hRetStep : evalOps tenv' [.returnOp rc.reg] = .ok tenv' := by
          simp [evalOps, evalOp, hLookup, Bind.bind, Except.bind]
        rw [hRetStep, list_getLast?_snoc (.returnOp rc.reg) rc.ops]
        dsimp only
        rw [hLookup]
        dsimp only
        rw [hTvTy, tensorType_bne_self]
        rfl

/-- Module-level corollary of `lowerToStableHLO_sound` for single-entry `ModuleOp`. -/
theorem lowerModuleToStableHLO_singleton_sound
    (modName : String) (d : LNIRDecl) (tensorLen fuel : Nat) (modOp : ModuleOp)
    (argVals : List Val) (targs : List TensorVal)
    (st st' : HeapState) (retVal : Val)
    (hLower : lowerModuleToStableHLO modName [d] tensorLen = some modOp)
    (hArgs : HLOArgsRel tensorLen st d.params argVals targs)
    (hEval : evalCode fuel (bindHLOParamEnv VarEnv.empty d.params argVals) st d.body =
      .ok (retVal, st')) :
    ∃ tv,
      HLOReturnRel d.retTy st' retVal tv ∧
      evalModuleOp modOp d.name targs = .ok tv := by
  dsimp [lowerModuleToStableHLO] at hLower
  cases hFn : lowerToStableHLO d tensorLen with
  | none => simp [hFn] at hLower
  | some fn =>
    simp [hFn] at hLower
    subst hLower
    have hName : fn.name = d.name := by
      dsimp [lowerToStableHLO] at hFn
      cases hI : initHLOParams tensorLen d.params with
      | none => simp [hI] at hFn
      | some out =>
        rcases out with ⟨Γ0, params⟩
        simp only [hI, Option.bind] at hFn
        cases hC : lowerCode Γ0 d.body 0 with
        | none => simp [hC] at hFn
        | some rc =>
          simp only [hC] at hFn
          cases hM : matchReturnKind d.retTy rc.outKind with
          | none => simp [hM] at hFn
          | some resTy =>
            simp only [hM, Option.some.injEq] at hFn
            subst hFn
            rfl
    rcases lowerToStableHLO_sound d tensorLen fuel fn argVals targs st st' retVal hFn hArgs hEval with
      ⟨tv, hRel, _, hEvFn⟩
    refine ⟨tv, hRel, ?_⟩
    simp [evalModuleOp, hName, hEvFn]

/-! ## 2. Non-Vacuity Witnesses (Scalar `ite` + Chained Tensor Pipeline) -/

/-- Scalar `ite` diamond declaration: `if a < b then b - a else a - b`. -/
def hloAbsDiffDecl : LNIRDecl :=
  { name := "hlo_abs_diff"
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := .i64
  , body :=
      .letBind 2 .i1 (.scalar (.binOp .lt (.var 0) (.var 1)))
        (.ite 2
          (.letBind 3 .i64 (.scalar (.binOp .sub (.var 1) (.var 0))) (.ret 3))
          (.letBind 4 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 4))) }

/-- End-to-end scalar/branching non-vacuity witness exercising `lowerToStableHLO_sound`
on `hloAbsDiffDecl` (`(3, 10) ↦ 7`). -/
theorem lowerToStableHLO_scalar_nonvacuous (fuel : Nat) :
    ∃ fn,
      lowerToStableHLO hloAbsDiffDecl 0 = some fn ∧
      evalCode fuel (bindHLOParamEnv VarEnv.empty hloAbsDiffDecl.params [.u64 3, .u64 10])
        HeapState.empty hloAbsDiffDecl.body = .ok (.u64 7, HeapState.empty) ∧
      evalFuncOp fn [mkScUi64 3#64, mkScUi64 10#64] = .ok (mkScUi64 7#64) := by
  cases hLow : lowerToStableHLO hloAbsDiffDecl 0 with
  | none => nomatch hLow
  | some fn =>
    have hArgs : HLOArgsRel 0 HeapState.empty hloAbsDiffDecl.params
        [.u64 3, .u64 10] [mkScUi64 3#64, mkScUi64 10#64] :=
      ⟨⟨.scalar .i64 none, rfl, ⟨3#64, rfl, rfl⟩, fun _ h => nomatch h⟩,
       ⟨.scalar .i64 none, rfl, ⟨10#64, rfl, rfl⟩, fun _ h => nomatch h⟩,
       trivial⟩
    have hEv : evalCode fuel
        (bindHLOParamEnv VarEnv.empty hloAbsDiffDecl.params [.u64 3, .u64 10])
        HeapState.empty hloAbsDiffDecl.body = .ok (.u64 7, HeapState.empty) := rfl
    rcases lowerToStableHLO_sound hloAbsDiffDecl 0 fuel fn
        [.u64 3, .u64 10] [mkScUi64 3#64, mkScUi64 10#64]
        HeapState.empty HeapState.empty (.u64 7) hLow hArgs hEv with
      ⟨tv, ⟨w, hEnc, rfl⟩, _, hExec⟩
    injection hEnc with hw
    subst hw
    exact ⟨fn, rfl, hEv, hExec⟩

/-- Chained tensor-pipeline declaration:
`n := sarrayLen x; z := saxpy 2 [x, y]; d := dotProduct [z, y]; return d[0]`. -/
def hloPipelineDecl : LNIRDecl :=
  { name := "saxpy_dot"
  , params :=
      [ { id := 0, name := "x", ty := .sarray .i64 }
      , { id := 1, name := "y", ty := .sarray .i64 } ]
  , retTy := .i64
  , body :=
      .letBind 2 .i64 (.sarrayLen 0)
        (.parFor 3 2 [0, 1] .i64 (.saxpy 2)
          (.parFor 4 2 [3, 1] .i64 .dotProduct
            (.letBind 5 .i64 (.scalar (.constU64 0))
              (.letBind 6 .i64 (.sarrayGet 4 5 .i64)
                (.ret 6))))) }

def pipelineInitHeap : HeapState :=
  { buffers :=
      [ { id := 2, exclusive := true, data := #[4, 5, 6] }
      , { id := 1, exclusive := true, data := #[1, 2, 3] } ]
  , nextId := 2 }

/-- End-to-end tensor-pipeline non-vacuity witness exercising `lowerToStableHLO_sound`
across `sarrayLen`, `saxpy`, `dotProduct`, and `sarrayGet` on
`x = #[1, 2, 3], y = #[4, 5, 6] ↦ ⟨2*x + y, y⟩ = 141`. -/
theorem lowerToStableHLO_pipeline_nonvacuous (fuel : Nat) (hFuel : 3 ≤ fuel) :
    ∃ fn st',
      lowerToStableHLO hloPipelineDecl 3 = some fn ∧
      evalCode fuel (bindHLOParamEnv VarEnv.empty hloPipelineDecl.params [.sarrayId 1, .sarrayId 2])
        pipelineInitHeap hloPipelineDecl.body = .ok (.u64 141, st') ∧
      evalFuncOp fn [mkVecUi64 #[1, 2, 3], mkVecUi64 #[4, 5, 6]] = .ok (mkScUi64 141#64) := by
  cases hLow : lowerToStableHLO hloPipelineDecl 3 with
  | none => nomatch hLow
  | some fn =>
    have hArgs : HLOArgsRel 3 pipelineInitHeap hloPipelineDecl.params
        [.sarrayId 1, .sarrayId 2] [mkVecUi64 #[1, 2, 3], mkVecUi64 #[4, 5, 6]] :=
      ⟨⟨.tensor1D 3, rfl, 1, { id := 1, exclusive := true, data := #[1, 2, 3] },
          rfl, Nat.le_succ 1, rfl, rfl, rfl⟩,
       ⟨.tensor1D 3, rfl, 2, { id := 2, exclusive := true, data := #[4, 5, 6] },
          rfl, Nat.le_refl 2, rfl, rfl, rfl⟩,
       trivial⟩
    have hNotGt : ¬ (3 > fuel) := by omega
    let st1 : HeapState :=
      { pipelineInitHeap with
        buffers := { id := 3, exclusive := true, data := #[6, 9, 12] } :: pipelineInitHeap.buffers
        nextId := 3 }
    let st2 : HeapState :=
      { st1 with
        buffers := { id := 4, exclusive := true, data := #[141] } :: st1.buffers
        nextId := 4 }
    have hEv : evalCode fuel
        (bindHLOParamEnv VarEnv.empty hloPipelineDecl.params [.sarrayId 1, .sarrayId 2])
        pipelineInitHeap hloPipelineDecl.body = .ok (.u64 141, st2) := by
      let env0 := bindHLOParamEnv VarEnv.empty hloPipelineDecl.params [.sarrayId 1, .sarrayId 2]
      let env2 := env0.bind 2 (.u64 3)
      have hs1 : evalParFor fuel env2 pipelineInitHeap 2 [0, 1] (.saxpy 2) =
          .ok (.sarrayId 3, st1) := by
        unfold evalParFor
        have he2 : env2 2 = some (.u64 3) := rfl
        rw [he2]
        have hn : (3 : UInt64).toNat = 3 := rfl
        simp only [hn, hNotGt, ↓reduceIte]
        rfl
      let env3 := env2.bind 3 (.sarrayId 3)
      have hs2 : evalParFor fuel env3 st1 2 [3, 1] .dotProduct =
          .ok (.sarrayId 4, st2) := by
        unfold evalParFor
        have he2 : env3 2 = some (.u64 3) := rfl
        rw [he2]
        have hn : (3 : UInt64).toNat = 3 := rfl
        simp only [hn, hNotGt, ↓reduceIte]
        rfl
      change evalCode fuel env0 pipelineInitHeap
        (.letBind 2 .i64 (.sarrayLen 0)
          (.parFor 3 2 [0, 1] .i64 (.saxpy 2)
            (.parFor 4 2 [3, 1] .i64 .dotProduct
              (.letBind 5 .i64 (.scalar (.constU64 0))
                (.letBind 6 .i64 (.sarrayGet 4 5 .i64)
                  (.ret 6)))))) = .ok (.u64 141, st2)
      unfold evalCode
      have he0 : evalExpr env0 pipelineInitHeap (.sarrayLen 0) = .ok (.u64 3, pipelineInitHeap) := rfl
      rw [he0]
      change evalCode fuel env2 pipelineInitHeap _ = _
      unfold evalCode
      rw [hs1]
      change evalCode fuel env3 st1 _ = _
      unfold evalCode
      rw [hs2]
      rfl
    rcases lowerToStableHLO_sound hloPipelineDecl 3 fuel fn
        [.sarrayId 1, .sarrayId 2] [mkVecUi64 #[1, 2, 3], mkVecUi64 #[4, 5, 6]]
        pipelineInitHeap st2 (.u64 141) hLow hArgs hEv with
      ⟨tv, ⟨w, hEnc, rfl⟩, _, hExec⟩
    injection hEnc with hw
    subst hw
    exact ⟨fn, st2, rfl, hEv, hExec⟩

/-! ## 3. Emitter Mutant Kills (`H1`..`H3`) -/

def hloSubSpecDecl : LNIRDecl :=
  { name := "spec_sub"
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := .i64
  , body := .letBind 2 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 2) }

/-- `H1` kill: swapping `subtract` operands (`v1 - v0` vs `v0 - v1`) changes `evalFuncOp`
on `(1#64, 2#64)`. -/
theorem hlo_mutant_h1_killed (fn : FuncOp)
    (hLow : lowerToStableHLO hloSubSpecDecl 0 = some fn) :
    evalFuncOp fn [mkScUi64 1#64, mkScUi64 2#64] ≠
      evalFuncOp hloMutantSubSwap [mkScUi64 1#64, mkScUi64 2#64] := by
  have hSpec : lowerToStableHLO hloSubSpecDecl 0 =
      some { name := "spec_sub"
           , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
           , result := scUi64Ty
           , body := [.subtract "t0" "v0" "v1", .returnOp "t0"] } := rfl
  rw [hSpec] at hLow
  injection hLow with hfn
  subst hfn
  have h1 : evalFuncOp
      { name := "spec_sub"
      , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
      , result := scUi64Ty
      , body := [.subtract "t0" "v0" "v1", .returnOp "t0"] }
      [mkScUi64 1#64, mkScUi64 2#64] = .ok (mkScUi64 (1#64 - 2#64)) := rfl
  have h2 : evalFuncOp hloMutantSubSwap [mkScUi64 1#64, mkScUi64 2#64] =
      .ok (mkScUi64 (2#64 - 1#64)) := rfl
  rw [h1, h2]
  intro h
  nomatch h

def hloShlSpecDecl : LNIRDecl :=
  { name := "spec_shl"
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := .i64
  , body := .letBind 2 .i64 (.scalar (.binOp .shl (.var 0) (.var 1))) (.ret 2) }

/-- `H2` kill: omitting the `& 63` shift-amount mask changes `evalFuncOp` on `(1#64, 64#64)`
(`1#64` vs `0#64`). -/
theorem hlo_mutant_h2_killed (fn : FuncOp)
    (hLow : lowerToStableHLO hloShlSpecDecl 0 = some fn) :
    evalFuncOp fn [mkScUi64 1#64, mkScUi64 64#64] ≠
      evalFuncOp hloMutantUnmaskedShl [mkScUi64 1#64, mkScUi64 64#64] := by
  have hSpec : lowerToStableHLO hloShlSpecDecl 0 =
      some { name := "spec_shl"
           , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
           , result := scUi64Ty
           , body :=
               [ .constant "t0" (mkScUi64 63#64)
               , .and "t1" "v1" "t0"
               , .shiftLeft "t2" "v0" "t1"
               , .returnOp "t2" ] } := rfl
  rw [hSpec] at hLow
  injection hLow with hfn
  subst hfn
  have h1 : evalFuncOp
      { name := "spec_shl"
      , params := [("v0", scUi64Ty), ("v1", scUi64Ty)]
      , result := scUi64Ty
      , body :=
          [ .constant "t0" (mkScUi64 63#64)
          , .and "t1" "v1" "t0"
          , .shiftLeft "t2" "v0" "t1"
          , .returnOp "t2" ] }
      [mkScUi64 1#64, mkScUi64 64#64] = .ok (mkScUi64 1#64) := rfl
  have h2 : evalFuncOp hloMutantUnmaskedShl [mkScUi64 1#64, mkScUi64 64#64] =
      .ok (mkScUi64 0#64) := rfl
  rw [h1, h2]
  intro h
  nomatch h

def hloDivSpecDecl : LNIRDecl :=
  { name := "spec_div"
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := .i64
  , body := .letBind 2 .i64 (.scalar (.binOp .div (.var 0) (.var 1))) (.ret 2) }

/-- `H3` kill: omitting the zero-divisor guard before `divide` triggers `.error .divisionByZero`
on `(7#64, 0#64)`, whereas `lowerToStableHLO` returns `.ok (mkScUi64 0#64)`. -/
theorem hlo_mutant_h3_killed (fn : FuncOp)
    (hLow : lowerToStableHLO hloDivSpecDecl 0 = some fn) :
    evalFuncOp fn [mkScUi64 7#64, mkScUi64 0#64] ≠
      evalFuncOp hloMutantUnguardedDiv [mkScUi64 7#64, mkScUi64 0#64] := by
  have hEv : evalCode 0 (bindHLOParamEnv VarEnv.empty hloDivSpecDecl.params [.u64 7, .u64 0])
      HeapState.empty hloDivSpecDecl.body = .ok (.u64 0, HeapState.empty) := rfl
  have hArgs : HLOArgsRel 0 HeapState.empty hloDivSpecDecl.params
      [.u64 7, .u64 0] [mkScUi64 7#64, mkScUi64 0#64] :=
    ⟨⟨.scalar .i64 none, rfl, ⟨7#64, rfl, rfl⟩, fun _ h => nomatch h⟩,
     ⟨.scalar .i64 none, rfl, ⟨0#64, rfl, rfl⟩, fun _ h => nomatch h⟩,
     trivial⟩
  rcases lowerToStableHLO_sound hloDivSpecDecl 0 0 fn
      [.u64 7, .u64 0] [mkScUi64 7#64, mkScUi64 0#64]
      HeapState.empty HeapState.empty (.u64 0) hLow hArgs hEv with
    ⟨tv, ⟨w, hEnc, rfl⟩, _, h1⟩
  injection hEnc with hw
  subst hw
  have h2 : evalFuncOp hloMutantUnguardedDiv [mkScUi64 7#64, mkScUi64 0#64] =
      .error .divisionByZero := rfl
  rw [h1, h2]
  intro h
  nomatch h

end LeanNative.Proofs
