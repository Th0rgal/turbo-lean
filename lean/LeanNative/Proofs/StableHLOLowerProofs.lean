import LeanNative.Proofs.StableHLOCodeProofs
import LeanNative.Backend.MLIRGPU

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
4. `MLIRGPU.lowerStableHLODeclFunc_roundtrip`, `lowerToStableHLO_canonical`, and
   `lowerToStableHLO_roundtrip`: syntactic/type canonicality and `parseFuncOp ∘ ppFuncOp`
   roundtrip corollaries for lowered StableHLO functions.
-/

namespace LeanNative.Backend.MLIRGPU

open LeanNative.IR StableHLOAst

private theorem ssaName_lit (s : String)
    (h1 : s.toList.isEmpty = false := by decide)
    (h2 : s.toList.all (fun c => c.isAlphanum || c == '_') = true := by decide) :
    CanonicalSSAName s := ⟨h1, h2⟩

private theorem const1D_canonical (tenv : TypeEnv) (d : String) (n : Nat) (w : UInt64)
    (hd : CanonicalSSAName d) :
    let ty : TensorType := { shape := [n], elem := .ui64 }
    let v : TensorVal := { ty := ty, data := Array.replicate ty.numElements w.toBitVec }
    CanonicalStableHLOOp tenv (.constant d v) ∧
    bindResult tenv (.constant d v) = tenv.bind d ty := by
  refine ⟨⟨hd, rfl, Or.inr ⟨n, rfl⟩, Array.size_replicate ..⟩, ?_⟩
  simp only [bindResult, resultTypeOf, Array.size_replicate, beq_self_eq_true, ↓reduceIte]

/-- The declaration emitter constructs lexically valid, well-typed covered operations. -/
theorem lowerStableHLODeclFunc_canonical (name : String) (kernel : ParallelKernelKind)
    (f : FuncOp) (hn : CanonicalSSAName name)
    (hf : lowerStableHLODeclFunc name kernel = some f) : CanonicalFuncOp f := by
  let ty : TensorType := { shape := [262144], elem := .ui64 }
  cases kernel with
  | mapScaleAdd scale bias =>
    simp only [lowerStableHLODeclFunc, bind, Option.bind, pure, Option.some.injEq] at hf
    subst hf; refine ⟨hn, ?_, ?_⟩
    · intro p hp; simp only [List.map, List.mem_singleton] at hp; subst hp; exact ssaName_lit _
    · dsimp only [List.map, List.foldl, CanonicalBody]
      have h0 := const1D_canonical (TypeEnv.empty.bind "in0" ty) "c_scale" 262144 scale (ssaName_lit _)
      refine ⟨h0.1, ?_⟩; rw [h0.2]
      have h1 := const1D_canonical ((TypeEnv.empty.bind "in0" ty).bind "c_scale" ty) "c_bias" 262144 bias (ssaName_lit _)
      refine ⟨h1.1, ?_⟩; rw [h1.2]
      dsimp only [CanonicalStableHLOOp, resultTypeOf, bindResult, TypeEnv.bind]
      exact ⟨⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, by decide⟩,
        ⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, by decide⟩, ⟨ssaName_lit _, by decide⟩, trivial⟩
  | zipAdd | zipMul =>
    simp only [lowerStableHLODeclFunc, bind, Option.bind, pure, Option.some.injEq] at hf
    subst hf; refine ⟨hn, ?_, ?_⟩
    · intro p hp; simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ssaName_lit _
    · dsimp only [List.map, List.foldl, CanonicalBody, CanonicalStableHLOOp, resultTypeOf, bindResult, TypeEnv.bind]
      exact ⟨⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, by decide⟩, ⟨ssaName_lit _, by decide⟩, trivial⟩
  | saxpy alpha =>
    simp only [lowerStableHLODeclFunc, bind, Option.bind, pure, Option.some.injEq] at hf
    subst hf; refine ⟨hn, ?_, ?_⟩
    · intro p hp; simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ssaName_lit _
    · dsimp only [List.map, List.foldl, CanonicalBody]
      have h0 := const1D_canonical ((TypeEnv.empty.bind "x" ty).bind "y" ty) "c_alpha" 262144 alpha (ssaName_lit _)
      refine ⟨h0.1, ?_⟩; rw [h0.2]
      dsimp only [CanonicalStableHLOOp, resultTypeOf, bindResult, TypeEnv.bind]
      exact ⟨⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, by decide⟩,
        ⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, by decide⟩, ⟨ssaName_lit _, by decide⟩, trivial⟩
  | dotProduct =>
    simp only [lowerStableHLODeclFunc, bind, Option.bind, pure, Option.some.injEq] at hf
    subst hf; refine ⟨hn, ?_, ?_⟩
    · intro p hp; simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ssaName_lit _
    · dsimp only [List.map, List.foldl, CanonicalBody, CanonicalStableHLOOp, resultTypeOf, bindResult, TypeEnv.bind]
      exact ⟨⟨ssaName_lit _, ssaName_lit _, ssaName_lit _, rfl, rfl, by decide⟩, ⟨ssaName_lit _, by decide⟩, trivial⟩
  | stencil1D3Pt _ _ _ | customScalar _ _ _ =>
    simp [lowerStableHLODeclFunc] at hf

/-- Every canonical lowered declaration function roundtrips through `parseFuncOp ∘ ppFuncOp`. -/
theorem lowerStableHLODeclFunc_roundtrip (name : String) (kernel : ParallelKernelKind)
    (f : FuncOp) (hn : CanonicalSSAName name)
    (hf : lowerStableHLODeclFunc name kernel = some f) :
    parseFuncOp (ppFuncOp f) = some f :=
  parseFuncOp_roundtrip f (lowerStableHLODeclFunc_canonical name kernel f hn hf)

end LeanNative.Backend.MLIRGPU

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.StableHLOLower
open LeanNative.Backend.LLVMLower (isI64Ty isI1Ty sameScalarTy)

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

/-! ## 4. Lowerer Canonicality & Roundtrip (`lowerToStableHLO_canonical`, `lowerToStableHLO_roundtrip`) -/

private theorem digitChar_alphanum (d : Nat) :
    ((digitChar d).isAlphanum || digitChar d == '_') = true := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => rfl

private theorem natDigitsAux_alphanum :
    ∀ (fuel n : Nat) (acc : List Char),
      acc.all (fun c => c.isAlphanum || c == '_') = true →
      (natDigitsAux fuel n acc).all (fun c => c.isAlphanum || c == '_') = true
  | 0, _, acc, hacc => hacc
  | fuel + 1, n, acc, hacc => by
    simp only [natDigitsAux]
    split
    · simp [digitChar_alphanum, hacc]
    · exact natDigitsAux_alphanum fuel (n / 10) _ (by simp [digitChar_alphanum, hacc])

private theorem ppInt_alphanum (n : Nat) :
    (ppInt n).toList.all (fun c => c.isAlphanum || c == '_') = true := by
  unfold ppInt natDigits
  rw [String.toList_ofList]
  exact natDigitsAux_alphanum (n + 1) n [] rfl

theorem canonicalSSAName_hloVarReg (v : VarId) : CanonicalSSAName (hloVarReg v) := by
  refine ⟨by simp [hloVarReg, String.toList_append], ?_⟩
  simp only [hloVarReg, String.toList_append, List.all_append, ppInt_alphanum, Bool.and_true]
  decide

theorem canonicalSSAName_hloTmpReg (k : Nat) : CanonicalSSAName (hloTmpReg k) := by
  refine ⟨by simp [hloTmpReg, String.toList_append], ?_⟩
  simp only [hloTmpReg, String.toList_append, List.all_append, ppInt_alphanum, Bool.and_true]
  decide

private theorem typeEnv_bind_self (tenv : TypeEnv) (r : String) (ty : TensorType) :
    (tenv.bind r ty) r = some ty := by
  simp [TypeEnv.bind]

private theorem typeEnv_bind_ne (tenv : TypeEnv) (r q : String) (ty : TensorType) (hne : q ≠ r) :
    (tenv.bind r ty) q = tenv q := by
  have hb : (q == r) = false := beq_eq_false_iff_ne.mpr hne
  simp [TypeEnv.bind, hb]

private theorem typeEnv_frame_trans (tenv tenv1 tenv2 : TypeEnv) (k k1 k2 : Nat)
    (h1 : k ≤ k1) (h2 : k1 ≤ k2)
    (hf1 : ∀ q, (∀ j, k ≤ j → j < k1 → q ≠ hloTmpReg j) → tenv1 q = tenv q)
    (hf2 : ∀ q, (∀ j, k1 ≤ j → j < k2 → q ≠ hloTmpReg j) → tenv2 q = tenv1 q) :
    ∀ q, (∀ j, k ≤ j → j < k2 → q ≠ hloTmpReg j) → tenv2 q = tenv q := by
  intro q hq
  rw [hf2 q (fun j hjk1 hjk2 => hq j (Nat.le_trans h1 hjk1) hjk2),
      hf1 q (fun j hjk hjk1 => hq j hjk (Nat.lt_of_lt_of_le hjk1 h2))]

/-- Static `TypeEnv` agreement and temporary-register freshness invariant for `HLOTyEnv`. -/
def HLOTypeEnvWF (Γ : HLOTyEnv) (tenv : TypeEnv) (k : Nat) : Prop :=
  ∀ v entry, Γ v = some entry →
    CanonicalSSAName entry.reg ∧
    tenv entry.reg = some entry.kind.tensorType ∧
    (∀ j, k ≤ j → entry.reg ≠ hloTmpReg j)

private theorem hloTypeEnvWF_frame (Γ : HLOTyEnv) (tenv tenv' : TypeEnv) (k k' : Nat)
    (hWF : HLOTypeEnvWF Γ tenv k) (hle : k ≤ k')
    (hFrame : ∀ q, (∀ j, k ≤ j → j < k' → q ≠ hloTmpReg j) → tenv' q = tenv q) :
    HLOTypeEnvWF Γ tenv' k' := by
  intro v entry hΓ
  obtain ⟨hn, hty, hfr⟩ := hWF v entry hΓ
  refine ⟨hn, ?_, fun j hj => hfr j (Nat.le_trans hle hj)⟩
  rw [hFrame entry.reg (fun j hjk _ => hfr j hjk)]
  exact hty

private theorem hloTypeEnvWF_bind (Γ : HLOTyEnv) (tenv : TypeEnv) (k : Nat)
    (dst : VarId) (r : String) (vk : HLOVarKind)
    (hWF : HLOTypeEnvWF Γ tenv k)
    (hr : CanonicalSSAName r)
    (hty : tenv r = some vk.tensorType)
    (hfr : ∀ j, k ≤ j → r ≠ hloTmpReg j) :
    HLOTypeEnvWF (Γ.bind dst ⟨r, vk⟩) tenv k := by
  intro v entry hΓ
  unfold HLOTyEnv.bind at hΓ
  by_cases hvd : (v == dst) = true
  · simp only [hvd, ↓reduceIte, Option.some.injEq] at hΓ
    subst hΓ
    exact ⟨hr, hty, hfr⟩
  · have hvf : (v == dst) = false := Bool.eq_false_iff.mpr hvd
    simp only [hvf, Bool.false_eq_true, ↓reduceIte] at hΓ
    exact hWF v entry hΓ

private theorem initHLOParamsAcc_canonical (tensorLen : Nat) (Γ : HLOTyEnv) (tenv : TypeEnv)
    (ps : List LNIRParam) (out : HLOTyEnv × List (String × TensorType))
    (hVar : HLOVarRegCanonical Γ)
    (hWF : HLOTypeEnvWF Γ tenv 0)
    (hInit : initHLOParamsAcc tensorLen Γ ps = some out) :
    (∀ p ∈ out.2, CanonicalSSAName p.1) ∧
    HLOTypeEnvWF out.1 (out.2.foldl (fun e (n, ty) => e.bind n ty) tenv) 0 := by
  induction ps generalizing Γ tenv out with
  | nil =>
    simp only [initHLOParamsAcc, Option.some.injEq] at hInit
    subst hInit
    exact ⟨(fun _ h => nomatch h), hWF⟩
  | cons p ps' ih =>
    dsimp [initHLOParamsAcc] at hInit
    cases hvk : paramVarKind tensorLen p.ty with
    | none => simp [hvk] at hInit
    | some vk =>
      simp only [hvk, Option.bind] at hInit
      cases hRest : initHLOParamsAcc tensorLen (Γ.bind p.id ⟨hloVarReg p.id, vk⟩) ps' with
      | none => simp [hRest] at hInit
      | some out1 =>
        simp only [hRest, Option.some.injEq] at hInit
        subst hInit
        have hVar1 : HLOVarRegCanonical (Γ.bind p.id ⟨hloVarReg p.id, vk⟩) := by
          intro x rx vkx hΓx
          unfold HLOTyEnv.bind at hΓx
          by_cases hxp : (x == p.id) = true
          · simp only [hxp, ↓reduceIte, Option.some.injEq] at hΓx
            have hx_eq : x = p.id := eq_of_beq hxp
            injection hΓx with hrx _
            exact hrx.symm.trans (congrArg hloVarReg hx_eq.symm)
          · have hxf : (x == p.id) = false := Bool.eq_false_iff.mpr hxp
            simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓx
            exact hVar x rx vkx hΓx
        have hWF1 : HLOTypeEnvWF (Γ.bind p.id ⟨hloVarReg p.id, vk⟩)
            (tenv.bind (hloVarReg p.id) vk.tensorType) 0 := by
          intro x entry hΓx
          unfold HLOTyEnv.bind at hΓx
          by_cases hxp : (x == p.id) = true
          · simp only [hxp, ↓reduceIte, Option.some.injEq] at hΓx
            subst hΓx
            exact ⟨canonicalSSAName_hloVarReg p.id, typeEnv_bind_self _ _ _,
              fun j _ => hloVarReg_ne_hloTmpReg p.id j⟩
          · have hxf : (x == p.id) = false := Bool.eq_false_iff.mpr hxp
            simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hΓx
            rcases entry with ⟨rx, vkx⟩
            have hrx := hVar x rx vkx hΓx
            subst hrx
            have hne : hloVarReg x ≠ hloVarReg p.id :=
              fun heq => hxp (beq_iff_eq.mpr (hloVarReg_injective heq))
            obtain ⟨hnx, htyx, hfrx⟩ := hWF x ⟨hloVarReg x, vkx⟩ hΓx
            exact ⟨hnx, (typeEnv_bind_ne tenv (hloVarReg p.id) (hloVarReg x) _ hne).trans htyx, hfrx⟩
        obtain ⟨hpRest, hWFRest⟩ := ih _ _ out1 hVar1 hWF1 hRest
        refine ⟨?_, hWFRest⟩
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact canonicalSSAName_hloVarReg p.id
        · exact hpRest q hq

/-- Compositional `TypeEnv` + `CanonicalBody` post-condition for straight-line lowered blocks. -/
def HLOTyBlockPost (tenv : TypeEnv) (k nextTmp : Nat) (reg : String) (outTy : TensorType)
    (ops : List StableHLOOp) : Prop :=
  k ≤ nextTmp ∧
  CanonicalSSAName reg ∧
  (∀ j, nextTmp ≤ j → reg ≠ hloTmpReg j) ∧
  CanonicalBody tenv ops ∧
  (ops.foldl bindResult tenv) reg = some outTy ∧
  (∀ q, (∀ j, k ≤ j → j < nextTmp → q ≠ hloTmpReg j) →
    (ops.foldl bindResult tenv) q = tenv q)

private theorem hloTyBlockPost_nil (tenv : TypeEnv) (k : Nat) (reg : String) (outTy : TensorType)
    (hr : CanonicalSSAName reg) (hfr : ∀ j, k ≤ j → reg ≠ hloTmpReg j)
    (hty : tenv reg = some outTy) :
    HLOTyBlockPost tenv k k reg outTy [] :=
  ⟨Nat.le_refl k, hr, hfr, trivial, hty, fun _ _ => rfl⟩

private theorem hloTyBlockPost_single (tenv : TypeEnv) (k : Nat) (op : StableHLOOp)
    (outTy : TensorType)
    (hOp : CanonicalStableHLOOp tenv op)
    (hBind : bindResult tenv op = tenv.bind (hloTmpReg k) outTy) :
    HLOTyBlockPost tenv k (k + 1) (hloTmpReg k) outTy [op] := by
  refine ⟨Nat.le_succ k, canonicalSSAName_hloTmpReg k,
    fun j hj => hloTmpReg_ne_of_ne (by omega), ⟨hOp, trivial⟩, ?_, ?_⟩
  · simp [hBind, typeEnv_bind_self]
  · intro q hq
    simp only [List.foldl_cons, List.foldl_nil, hBind]
    exact typeEnv_bind_ne _ _ _ _ (hq k (Nat.le_refl k) (Nat.lt_succ_self k))

private theorem hloTyBlockPost_cons (tenv : TypeEnv) (k nextTmp : Nat)
    (op : StableHLOOp) (ops : List StableHLOOp) (opTy outTy : TensorType) (reg : String)
    (hOp : CanonicalStableHLOOp tenv op)
    (hBind : bindResult tenv op = tenv.bind (hloTmpReg k) opTy)
    (hRest : HLOTyBlockPost (tenv.bind (hloTmpReg k) opTy) (k + 1) nextTmp reg outTy ops) :
    HLOTyBlockPost tenv k nextTmp reg outTy (op :: ops) := by
  obtain ⟨hle, hr, hfr, hBody, hOut, hFrame⟩ := hRest
  refine ⟨Nat.le_trans (Nat.le_succ k) hle, hr, hfr, ⟨hOp, ?_⟩, ?_, ?_⟩
  · rwa [hBind]
  · simpa [List.foldl_cons, hBind] using hOut
  · intro q hq
    simp only [List.foldl_cons, hBind]
    rw [hFrame q (fun j hj1 hj2 => hq j (by omega) hj2)]
    exact typeEnv_bind_ne _ _ _ _ (hq k (Nat.le_refl k) (by omega))

private theorem hloTyBlockPost_seq (tenv : TypeEnv) (k k1 k2 : Nat)
    (r1 r2 : String) (ty1 ty2 : TensorType) (ops1 ops2 : List StableHLOOp)
    (h1 : HLOTyBlockPost tenv k k1 r1 ty1 ops1)
    (h2 : HLOTyBlockPost (ops1.foldl bindResult tenv) k1 k2 r2 ty2 ops2) :
    HLOTyBlockPost tenv k k2 r2 ty2 (ops1 ++ ops2) := by
  obtain ⟨hle1, _, _, hB1, _, hF1⟩ := h1
  obtain ⟨hle2, hr2, hfr2, hB2, hOut2, hF2⟩ := h2
  refine ⟨Nat.le_trans hle1 hle2, hr2, hfr2,
    (CanonicalBody.append tenv ops1 ops2).mpr ⟨hB1, hB2⟩, ?_, ?_⟩
  · rwa [List.foldl_append]
  · intro q hq
    rw [List.foldl_append]
    exact typeEnv_frame_trans tenv (ops1.foldl bindResult tenv) _ k k1 k2 hle1 hle2 hF1 hF2 q hq

/-! ### Single-op canonicality & `bindResult` lemmas -/

private theorem op_const_sc (tenv : TypeEnv) (m : Nat) (w : BitVec 64) :
    CanonicalStableHLOOp tenv (.constant (hloTmpReg m) (mkScUi64 w)) ∧
    bindResult tenv (.constant (hloTmpReg m) (mkScUi64 w)) = tenv.bind (hloTmpReg m) scUi64Ty :=
  ⟨⟨canonicalSSAName_hloTmpReg m, rfl, Or.inl rfl, rfl⟩, rfl⟩

private theorem op_add (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.add (hloTmpReg m) a b) ∧
    bindResult tenv (.add (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.add (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_sub (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.subtract (hloTmpReg m) a b) ∧
    bindResult tenv (.subtract (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.subtract (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_mul (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.multiply (hloTmpReg m) a b) ∧
    bindResult tenv (.multiply (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.multiply (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_div (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.divide (hloTmpReg m) a b) ∧
    bindResult tenv (.divide (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.divide (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_rem (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.remainder (hloTmpReg m) a b) ∧
    bindResult tenv (.remainder (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.remainder (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_and (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.and (hloTmpReg m) a b) ∧
    bindResult tenv (.and (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.and (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_or (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.or (hloTmpReg m) a b) ∧
    bindResult tenv (.or (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.or (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_xor (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.xor (hloTmpReg m) a b) ∧
    bindResult tenv (.xor (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.xor (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_shl (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.shiftLeft (hloTmpReg m) a b) ∧
    bindResult tenv (.shiftLeft (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.shiftLeft (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_shr (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.shiftRightLogical (hloTmpReg m) a b) ∧
    bindResult tenv (.shiftRightLogical (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.shiftRightLogical (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_sar (tenv : TypeEnv) (m : Nat) (a b : String) (ty : TensorType)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some ty) (htb : tenv b = some ty) :
    CanonicalStableHLOOp tenv (.shiftRightArithmetic (hloTmpReg m) a b) ∧
    bindResult tenv (.shiftRightArithmetic (hloTmpReg m) a b) = tenv.bind (hloTmpReg m) ty := by
  have hr : resultTypeOf tenv (.shiftRightArithmetic (hloTmpReg m) a b) = some ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_cmp_sc (tenv : TypeEnv) (m : Nat) (a b : String) (dir : CompareDir)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some scUi64Ty) (htb : tenv b = some scUi64Ty) :
    CanonicalStableHLOOp tenv (.compare (hloTmpReg m) a b dir) ∧
    bindResult tenv (.compare (hloTmpReg m) a b dir) = tenv.bind (hloTmpReg m) scI1Ty := by
  have hr : resultTypeOf tenv (.compare (hloTmpReg m) a b dir) = some scI1Ty := by
    simp [resultTypeOf, hta, htb, tensorType_beq_refl, scUi64Ty, scI1Ty]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_select_sc (tenv : TypeEnv) (m : Nat) (p t e : String)
    (hp : CanonicalSSAName p) (ht : CanonicalSSAName t) (he : CanonicalSSAName e)
    (htp : tenv p = some scI1Ty) (htt : tenv t = some scUi64Ty) (hte : tenv e = some scUi64Ty) :
    CanonicalStableHLOOp tenv (.select (hloTmpReg m) p t e) ∧
    bindResult tenv (.select (hloTmpReg m) p t e) = tenv.bind (hloTmpReg m) scUi64Ty := by
  have hr : resultTypeOf tenv (.select (hloTmpReg m) p t e) = some scUi64Ty := by
    simp [resultTypeOf, htp, htt, hte, tensorType_beq_refl, scUi64Ty, scI1Ty,
      show (ElemType.i1 == ElemType.i1) = true from rfl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hp, ht, he, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_convert (tenv : TypeEnv) (m : Nat) (s : String) (ty : TensorType)
    (outElem : ElemType) (hs : CanonicalSSAName s) (hts : tenv s = some ty) :
    CanonicalStableHLOOp tenv (.convert (hloTmpReg m) s outElem) ∧
    bindResult tenv (.convert (hloTmpReg m) s outElem) =
      tenv.bind (hloTmpReg m) { ty with elem := outElem } := by
  have hr : resultTypeOf tenv (.convert (hloTmpReg m) s outElem) = some { ty with elem := outElem } := by
    simp [resultTypeOf, hts]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hs, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_broadcast_sc (tenv : TypeEnv) (m n : Nat) (s : String)
    (hs : CanonicalSSAName s) (hts : tenv s = some scUi64Ty) :
    CanonicalStableHLOOp tenv (.broadcastInDim (hloTmpReg m) s [n] []) ∧
    bindResult tenv (.broadcastInDim (hloTmpReg m) s [n] []) =
      tenv.bind (hloTmpReg m) (vecUi64Ty n) := by
  have hr : resultTypeOf tenv (.broadcastInDim (hloTmpReg m) s [n] []) = some (vecUi64Ty n) := by
    simp [resultTypeOf, hts, scUi64Ty, vecUi64Ty, dimsStrict]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hs, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_dot_1d (tenv : TypeEnv) (m n : Nat) (a b : String)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some (vecUi64Ty n)) (htb : tenv b = some (vecUi64Ty n)) :
    CanonicalStableHLOOp tenv (.dotGeneral (hloTmpReg m) a b [] [] [0] [0] []) ∧
    bindResult tenv (.dotGeneral (hloTmpReg m) a b [] [] [0] [0] []) =
      tenv.bind (hloTmpReg m) scUi64Ty := by
  have hr : resultTypeOf tenv (.dotGeneral (hloTmpReg m) a b [] [] [0] [0] []) = some scUi64Ty := by
    simp [resultTypeOf, hta, htb, vecUi64Ty, scUi64Ty, dotOperandOk_1d,
      show (ElemType.ui64 == ElemType.ui64) = true from rfl]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, ha, hb, rfl, rfl, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_reshape_sc_to_vec1 (tenv : TypeEnv) (m : Nat) (s : String)
    (hs : CanonicalSSAName s) (hts : tenv s = some scUi64Ty) :
    CanonicalStableHLOOp tenv (.reshape (hloTmpReg m) s [1]) ∧
    bindResult tenv (.reshape (hloTmpReg m) s [1]) =
      tenv.bind (hloTmpReg m) (vecUi64Ty 1) := by
  have hr : resultTypeOf tenv (.reshape (hloTmpReg m) s [1]) = some (vecUi64Ty 1) := by
    simp [resultTypeOf, hts, scUi64Ty, vecUi64Ty]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hs, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_reshape_vec1_to_sc (tenv : TypeEnv) (m : Nat) (s : String)
    (hs : CanonicalSSAName s) (hts : tenv s = some (vecUi64Ty 1)) :
    CanonicalStableHLOOp tenv (.reshape (hloTmpReg m) s []) ∧
    bindResult tenv (.reshape (hloTmpReg m) s []) =
      tenv.bind (hloTmpReg m) scUi64Ty := by
  have hr : resultTypeOf tenv (.reshape (hloTmpReg m) s []) = some scUi64Ty := by
    simp [resultTypeOf, hts, vecUi64Ty, scUi64Ty]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hs, by simp [hr]⟩, by simp [bindResult, hr]⟩

private theorem op_slice_one (tenv : TypeEnv) (m n idx : Nat) (s : String)
    (hs : CanonicalSSAName s) (hts : tenv s = some (vecUi64Ty n)) (hIdx : idx < n) :
    CanonicalStableHLOOp tenv (.slice (hloTmpReg m) s [idx] [idx + 1] [1]) ∧
    bindResult tenv (.slice (hloTmpReg m) s [idx] [idx + 1] [1]) =
      tenv.bind (hloTmpReg m) (vecUi64Ty 1) := by
  have hdim : sliceOutDim n idx (idx + 1) 1 = some 1 := by
    unfold sliceOutDim
    have hc : (1 == 0 || decide (idx > idx + 1) || decide (idx + 1 > n)) = false := by
      simp [Bool.or_eq_false_iff]; omega
    rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]; congr 1; omega
  have hr : resultTypeOf tenv (.slice (hloTmpReg m) s [idx] [idx + 1] [1]) = some (vecUi64Ty 1) := by
    simp [resultTypeOf, hts, vecUi64Ty, sliceOutDims, hdim, Bind.bind, Except.bind]
  exact ⟨⟨canonicalSSAName_hloTmpReg m, hs, by simp [hr]⟩, by simp [bindResult, hr]⟩

/-! ### Multi-op emitter helpers (`emitHLODivRem`, `emitHLOShiftLogical`, `emitHLOSar`, `emitHLOCmp`) -/

private theorem emitHLODivRem_canonical (tenv : TypeEnv) (k : Nat) (isRem : Bool) (a b : String)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hfa : ∀ j, k ≤ j → a ≠ hloTmpReg j) (hfb : ∀ j, k ≤ j → b ≠ hloTmpReg j)
    (hta : tenv a = some scUi64Ty) (htb : tenv b = some scUi64Ty) :
    let (res, nextTmp, ops) := emitHLODivRem k isRem a b
    HLOTyBlockPost tenv k nextTmp res scUi64Ty ops := by
  dsimp only [emitHLODivRem]
  let e1 := tenv.bind (hloTmpReg k) scUi64Ty
  let e2 := e1.bind (hloTmpReg (k + 1)) scUi64Ty
  let e3 := e2.bind (hloTmpReg (k + 2)) scI1Ty
  let e4 := e3.bind (hloTmpReg (k + 3)) scUi64Ty
  let e5 := e4.bind (hloTmpReg (k + 4)) scUi64Ty
  have hb2 : e2 b = some scUi64Ty := by
    dsimp only [e2, e1]
    rw [typeEnv_bind_ne _ _ _ _ (hfb (k + 1) (by omega)), typeEnv_bind_ne _ _ _ _ (hfb k (by omega))]
    exact htb
  have hc0_2 : e2 (hloTmpReg k) = some scUi64Ty := by
    dsimp only [e2, e1]
    rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), typeEnv_bind_self]
  have hz_3 : e3 (hloTmpReg (k + 2)) = some scI1Ty := typeEnv_bind_self _ _ _
  have hc1_3 : e3 (hloTmpReg (k + 1)) = some scUi64Ty := by
    dsimp only [e3, e2]
    rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), typeEnv_bind_self]
  have hb3 : e3 b = some scUi64Ty := by
    dsimp only [e3]
    rw [typeEnv_bind_ne _ _ _ _ (hfb (k + 2) (by omega))]; exact hb2
  have ha4 : e4 a = some scUi64Ty := by
    dsimp only [e4, e3, e2, e1]
    rw [typeEnv_bind_ne _ _ _ _ (hfa (k + 3) (by omega)),
        typeEnv_bind_ne _ _ _ _ (hfa (k + 2) (by omega)),
        typeEnv_bind_ne _ _ _ _ (hfa (k + 1) (by omega)),
        typeEnv_bind_ne _ _ _ _ (hfa k (by omega))]
    exact hta
  have hs4 : e4 (hloTmpReg (k + 3)) = some scUi64Ty := typeEnv_bind_self _ _ _
  have hdiv : CanonicalStableHLOOp e4 (if isRem then .remainder (hloTmpReg (k + 4)) a (hloTmpReg (k + 3))
      else .divide (hloTmpReg (k + 4)) a (hloTmpReg (k + 3))) ∧
      bindResult e4 (if isRem then .remainder (hloTmpReg (k + 4)) a (hloTmpReg (k + 3))
      else .divide (hloTmpReg (k + 4)) a (hloTmpReg (k + 3))) = e5 := by
    cases isRem
    · exact op_div e4 (k + 4) a (hloTmpReg (k + 3)) scUi64Ty ha (canonicalSSAName_hloTmpReg _) ha4 hs4
    · exact op_rem e4 (k + 4) a (hloTmpReg (k + 3)) scUi64Ty ha (canonicalSSAName_hloTmpReg _) ha4 hs4
  have hz_5 : e5 (hloTmpReg (k + 2)) = some scI1Ty := by
    dsimp only [e5, e4]
    rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
        typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega))]
    exact hz_3
  have hfb_name : CanonicalSSAName (if isRem then a else hloTmpReg k) := by
    cases isRem
    · exact canonicalSSAName_hloTmpReg k
    · exact ha
  have hfb_ty : e5 (if isRem then a else hloTmpReg k) = some scUi64Ty := by
    cases isRem
    · simp only [Bool.false_eq_true, ↓reduceIte, e5, e4, e3]
      rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
          typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
          typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega))]
      exact hc0_2
    · simp only [↓reduceIte, e5]
      rw [typeEnv_bind_ne _ _ _ _ (hfa (k + 4) (by omega))]; exact ha4
  have hraw_5 : e5 (hloTmpReg (k + 4)) = some scUi64Ty := typeEnv_bind_self _ _ _
  have s0 := op_const_sc tenv k 0#64
  have s1 := op_const_sc e1 (k + 1) 1#64
  have s2 := op_cmp_sc e2 (k + 2) b (hloTmpReg k) .eq hb (canonicalSSAName_hloTmpReg _) hb2 hc0_2
  have s3 := op_select_sc e3 (k + 3) (hloTmpReg (k + 2)) (hloTmpReg (k + 1)) b
    (canonicalSSAName_hloTmpReg _) (canonicalSSAName_hloTmpReg _) hb hz_3 hc1_3 hb3
  have s5 := op_select_sc e5 (k + 5) (hloTmpReg (k + 2)) (if isRem then a else hloTmpReg k)
    (hloTmpReg (k + 4)) (canonicalSSAName_hloTmpReg _) hfb_name (canonicalSSAName_hloTmpReg _)
    hz_5 hfb_ty hraw_5
  exact hloTyBlockPost_cons tenv k (k + 6) _ _ _ _ _ s0.1 s0.2
    (hloTyBlockPost_cons e1 (k + 1) (k + 6) _ _ _ _ _ s1.1 s1.2
      (hloTyBlockPost_cons e2 (k + 2) (k + 6) _ _ _ _ _ s2.1 s2.2
        (hloTyBlockPost_cons e3 (k + 3) (k + 6) _ _ _ _ _ s3.1 s3.2
          (hloTyBlockPost_cons e4 (k + 4) (k + 6) _ _ _ _ _ hdiv.1 hdiv.2
            (hloTyBlockPost_single e5 (k + 5) _ _ s5.1 s5.2)))))

private theorem emitHLOShiftLogical_canonical (tenv : TypeEnv) (k : Nat) (isRight : Bool) (a b : String)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hfa : ∀ j, k ≤ j → a ≠ hloTmpReg j) (hfb : ∀ j, k ≤ j → b ≠ hloTmpReg j)
    (hta : tenv a = some scUi64Ty) (htb : tenv b = some scUi64Ty) :
    let (res, nextTmp, ops) := emitHLOShiftLogical k isRight a b
    HLOTyBlockPost tenv k nextTmp res scUi64Ty ops := by
  dsimp only [emitHLOShiftLogical]
  let e1 := tenv.bind (hloTmpReg k) scUi64Ty
  let e2 := e1.bind (hloTmpReg (k + 1)) scUi64Ty
  have hb1 : e1 b = some scUi64Ty := by
    dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hfb k (by omega))]; exact htb
  have ha2 : e2 a = some scUi64Ty := by
    dsimp only [e2, e1]
    rw [typeEnv_bind_ne _ _ _ _ (hfa (k + 1) (by omega)), typeEnv_bind_ne _ _ _ _ (hfa k (by omega))]
    exact hta
  have s0 := op_const_sc tenv k 63#64
  have s1 := op_and e1 (k + 1) b (hloTmpReg k) scUi64Ty hb (canonicalSSAName_hloTmpReg _)
    hb1 (typeEnv_bind_self _ _ _)
  have s2 : CanonicalStableHLOOp e2 (if isRight then .shiftRightLogical (hloTmpReg (k + 2)) a (hloTmpReg (k + 1))
      else .shiftLeft (hloTmpReg (k + 2)) a (hloTmpReg (k + 1))) ∧
      bindResult e2 (if isRight then .shiftRightLogical (hloTmpReg (k + 2)) a (hloTmpReg (k + 1))
      else .shiftLeft (hloTmpReg (k + 2)) a (hloTmpReg (k + 1))) = e2.bind (hloTmpReg (k + 2)) scUi64Ty := by
    cases isRight
    · exact op_shl e2 (k + 2) a (hloTmpReg (k + 1)) scUi64Ty ha (canonicalSSAName_hloTmpReg _) ha2 (typeEnv_bind_self _ _ _)
    · exact op_shr e2 (k + 2) a (hloTmpReg (k + 1)) scUi64Ty ha (canonicalSSAName_hloTmpReg _) ha2 (typeEnv_bind_self _ _ _)
  exact hloTyBlockPost_cons tenv k (k + 3) _ _ _ _ _ s0.1 s0.2
    (hloTyBlockPost_cons e1 (k + 1) (k + 3) _ _ _ _ _ s1.1 s1.2
      (hloTyBlockPost_single e2 (k + 2) _ _ s2.1 s2.2))

private theorem emitHLOSar_canonical (tenv : TypeEnv) (k : Nat) (a b : String)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hfa : ∀ j, k ≤ j → a ≠ hloTmpReg j) (hfb : ∀ j, k ≤ j → b ≠ hloTmpReg j)
    (hta : tenv a = some scUi64Ty) (htb : tenv b = some scUi64Ty) :
    let (res, nextTmp, ops) := emitHLOSar k a b
    HLOTyBlockPost tenv k nextTmp res scUi64Ty ops := by
  dsimp only [emitHLOSar]
  let e1 := tenv.bind (hloTmpReg k) scUi64Ty
  let e2 := e1.bind (hloTmpReg (k + 1)) scUi64Ty
  let e3 := e2.bind (hloTmpReg (k + 2)) scI64Ty
  let e4 := e3.bind (hloTmpReg (k + 3)) scI64Ty
  let e5 := e4.bind (hloTmpReg (k + 4)) scI64Ty
  have hb1 : e1 b = some scUi64Ty := by
    dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hfb k (by omega))]; exact htb
  have ha2 : e2 a = some scUi64Ty := by
    dsimp only [e2, e1]
    rw [typeEnv_bind_ne _ _ _ _ (hfa (k + 1) (by omega)), typeEnv_bind_ne _ _ _ _ (hfa k (by omega))]
    exact hta
  have hamt3 : e3 (hloTmpReg (k + 1)) = some scUi64Ty := by
    dsimp only [e3, e2]
    rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), typeEnv_bind_self]
  have hls4 : e4 (hloTmpReg (k + 2)) = some scI64Ty := by
    dsimp only [e4, e3]
    rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)), typeEnv_bind_self]
  have s0 := op_const_sc tenv k 63#64
  have s1 := op_and e1 (k + 1) b (hloTmpReg k) scUi64Ty hb (canonicalSSAName_hloTmpReg _)
    hb1 (typeEnv_bind_self _ _ _)
  have s2 := op_convert e2 (k + 2) a scUi64Ty .i64 ha ha2
  have s3 := op_convert e3 (k + 3) (hloTmpReg (k + 1)) scUi64Ty .i64 (canonicalSSAName_hloTmpReg _) hamt3
  have s4 := op_sar e4 (k + 4) (hloTmpReg (k + 2)) (hloTmpReg (k + 3)) scI64Ty
    (canonicalSSAName_hloTmpReg _) (canonicalSSAName_hloTmpReg _) hls4 (typeEnv_bind_self _ _ _)
  have s5 := op_convert e5 (k + 5) (hloTmpReg (k + 4)) scI64Ty .ui64
    (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
  exact hloTyBlockPost_cons tenv k (k + 6) _ _ _ _ _ s0.1 s0.2
    (hloTyBlockPost_cons e1 (k + 1) (k + 6) _ _ _ _ _ s1.1 s1.2
      (hloTyBlockPost_cons e2 (k + 2) (k + 6) _ _ _ _ _ s2.1 s2.2
        (hloTyBlockPost_cons e3 (k + 3) (k + 6) _ _ _ _ _ s3.1 s3.2
          (hloTyBlockPost_cons e4 (k + 4) (k + 6) _ _ _ _ _ s4.1 s4.2
            (hloTyBlockPost_single e5 (k + 5) _ _ s5.1 s5.2)))))

private theorem emitHLOCmp_canonical (tenv : TypeEnv) (k : Nat) (dir : CompareDir) (a b : String)
    (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hta : tenv a = some scUi64Ty) (htb : tenv b = some scUi64Ty) :
    let (res, nextTmp, ops) := emitHLOCmp k dir a b
    HLOTyBlockPost tenv k nextTmp res scUi64Ty ops := by
  dsimp only [emitHLOCmp]
  let e1 := tenv.bind (hloTmpReg k) scI1Ty
  have s0 := op_cmp_sc tenv k a b dir ha hb hta htb
  have s1 := op_convert e1 (k + 1) (hloTmpReg k) scI1Ty .ui64
    (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
  exact hloTyBlockPost_cons tenv k (k + 2) _ _ _ _ _ s0.1 s0.2
    (hloTyBlockPost_single e1 (k + 1) _ _ s1.1 s1.2)

private theorem lowerHLOBinOpStep_canonical (tenv : TypeEnv) (k : Nat) (op : BinOp)
    (rl rr r : HLOScalarRes)
    (hL : HLOTyBlockPost tenv k rl.nextTmp rl.reg scUi64Ty rl.ops)
    (hR : HLOTyBlockPost (rl.ops.foldl bindResult tenv) rl.nextTmp rr.nextTmp rr.reg scUi64Ty rr.ops)
    (hStep : lowerHLOBinOpStep op rl rr = some r) :
    HLOTyBlockPost tenv k r.nextTmp r.reg scUi64Ty r.ops := by
  have hPfx := hloTyBlockPost_seq tenv k rl.nextTmp rr.nextTmp rl.reg rr.reg scUi64Ty scUi64Ty
    rl.ops rr.ops hL hR
  let tenv2 := (rl.ops ++ rr.ops).foldl bindResult tenv
  have hta : tenv2 rl.reg = some scUi64Ty := by
    dsimp only [tenv2]
    rw [List.foldl_append, hR.2.2.2.2.2 rl.reg (fun j hj _ => hL.2.2.1 j hj)]
    exact hL.2.2.2.2.1
  have htb : tenv2 rr.reg = some scUi64Ty := by
    dsimp only [tenv2]
    rw [List.foldl_append]
    exact hR.2.2.2.2.1
  have hfa : ∀ j, rr.nextTmp ≤ j → rl.reg ≠ hloTmpReg j :=
    fun j hj => hL.2.2.1 j (Nat.le_trans hR.1 hj)
  have hfb : ∀ j, rr.nextTmp ≤ j → rr.reg ≠ hloTmpReg j := hR.2.2.1
  have ha := hL.2.1
  have hb := hR.2.1
  cases htl : rl.ty <;> simp only [lowerHLOBinOpStep, htl] at hStep <;> try contradiction
  · -- rl.ty = i1
    cases htr : rr.ty <;> simp only [htr] at hStep <;> try contradiction
    cases op <;> simp only [Option.some.injEq] at hStep <;> try contradiction
    subst hStep
    exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
      (emitHLOCmp_canonical tenv2 rr.nextTmp .eq rl.reg rr.reg ha hb hta htb)
  · -- rl.ty = i64
    cases htr : rr.ty <;> simp only [htr] at hStep <;> try contradiction
    cases op <;> simp only [lowerHLOBinOp64, Option.some.injEq] at hStep <;> try contradiction
    all_goals subst hStep
    · have s := op_add tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · have s := op_sub tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · have s := op_mul tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLODivRem_canonical tenv2 rr.nextTmp false rl.reg rr.reg ha hb hfa hfb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLODivRem_canonical tenv2 rr.nextTmp true rl.reg rr.reg ha hb hfa hfb hta htb)
    · have s := op_and tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · have s := op_or tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · have s := op_xor tenv2 rr.nextTmp rl.reg rr.reg scUi64Ty ha hb hta htb
      exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (hloTyBlockPost_single tenv2 rr.nextTmp _ _ s.1 s.2)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOShiftLogical_canonical tenv2 rr.nextTmp false rl.reg rr.reg ha hb hfa hfb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOShiftLogical_canonical tenv2 rr.nextTmp true rl.reg rr.reg ha hb hfa hfb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOSar_canonical tenv2 rr.nextTmp rl.reg rr.reg ha hb hfa hfb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOCmp_canonical tenv2 rr.nextTmp .eq rl.reg rr.reg ha hb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOCmp_canonical tenv2 rr.nextTmp .lt rl.reg rr.reg ha hb hta htb)
    · exact hloTyBlockPost_seq tenv k rr.nextTmp _ _ _ scUi64Ty scUi64Ty (rl.ops ++ rr.ops) _ hPfx
        (emitHLOCmp_canonical tenv2 rr.nextTmp .le rl.reg rr.reg ha hb hta htb)

/-! ### `lowerScalarExpr`, `lowerScalarCode`, `lowerParKernel`, and `lowerCode` canonicality -/

private theorem lowerScalarExpr_canonical (Γ : HLOTyEnv) (se : ScalarExpr) (tenv : TypeEnv)
    (k : Nat) (rs : HLOScalarRes)
    (hWF : HLOTypeEnvWF Γ tenv k)
    (hLow : lowerScalarExpr Γ se k = some rs) :
    HLOTyBlockPost tenv k rs.nextTmp rs.reg scUi64Ty rs.ops := by
  induction se generalizing tenv k rs with
  | constU64 val =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    have s := op_const_sc tenv k val.toBitVec
    exact hloTyBlockPost_single tenv k _ _ s.1 s.2
  | constBool b =>
    simp only [lowerScalarExpr, Option.some.injEq] at hLow
    subst hLow
    have s := op_const_sc tenv k (if b then 1#64 else 0#64)
    exact hloTyBlockPost_single tenv k _ _ s.1 s.2
  | var id =>
    dsimp [lowerScalarExpr] at hLow
    cases hΓ : Γ id with
    | none => simp [hΓ] at hLow
    | some entry =>
      rcases entry with ⟨r, vk⟩
      cases vk with
      | tensor1D _ => simp [hΓ] at hLow
      | scalar ty kn =>
        simp only [hΓ] at hLow
        split at hLow
        · simp only [Option.some.injEq] at hLow
          subst hLow
          obtain ⟨hr, hty, hfr⟩ := hWF id ⟨r, .scalar ty kn⟩ hΓ
          exact hloTyBlockPost_nil tenv k r scUi64Ty hr hfr hty
        · simp at hLow
  | unaryOp op arg ih =>
    dsimp [lowerScalarExpr] at hLow
    cases hArg : lowerScalarExpr Γ arg k with
    | none => simp [hArg] at hLow
    | some ra =>
      simp only [hArg, Option.bind] at hLow
      have hA := ih tenv k ra hWF hArg
      let tenvA := ra.ops.foldl bindResult tenv
      cases op with
      | clz256 => simp at hLow
      | not =>
        by_cases h64 : isI64Ty ra.ty = true
        · simp only [h64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          have s0 := op_const_sc tenvA ra.nextTmp (BitVec.ofNat 64 0xffffffffffffffff)
          let e1 := tenvA.bind (hloTmpReg ra.nextTmp) scUi64Ty
          have hra1 : e1 ra.reg = some scUi64Ty := by
            dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hA.2.2.1 _ (Nat.le_refl _))]; exact hA.2.2.2.2.1
          have s1 := op_xor e1 (ra.nextTmp + 1) ra.reg (hloTmpReg ra.nextTmp) scUi64Ty
            hA.2.1 (canonicalSSAName_hloTmpReg _) hra1 (typeEnv_bind_self _ _ _)
          exact hloTyBlockPost_seq tenv k ra.nextTmp _ _ _ scUi64Ty scUi64Ty ra.ops _ hA
            (hloTyBlockPost_cons tenvA ra.nextTmp (ra.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
              (hloTyBlockPost_single e1 (ra.nextTmp + 1) _ _ s1.1 s1.2))
        · simp only [h64, Bool.false_eq_true, ↓reduceIte] at hLow
          by_cases h1 : isI1Ty ra.ty = true
          · simp only [h1, ↓reduceIte, Option.some.injEq] at hLow
            subst hLow
            have s0 := op_const_sc tenvA ra.nextTmp 1#64
            let e1 := tenvA.bind (hloTmpReg ra.nextTmp) scUi64Ty
            have hra1 : e1 ra.reg = some scUi64Ty := by
              dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hA.2.2.1 _ (Nat.le_refl _))]; exact hA.2.2.2.2.1
            have s1 := op_xor e1 (ra.nextTmp + 1) ra.reg (hloTmpReg ra.nextTmp) scUi64Ty
              hA.2.1 (canonicalSSAName_hloTmpReg _) hra1 (typeEnv_bind_self _ _ _)
            exact hloTyBlockPost_seq tenv k ra.nextTmp _ _ _ scUi64Ty scUi64Ty ra.ops _ hA
              (hloTyBlockPost_cons tenvA ra.nextTmp (ra.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
                (hloTyBlockPost_single e1 (ra.nextTmp + 1) _ _ s1.1 s1.2))
          · simp [h1] at hLow
      | neg =>
        by_cases h64 : isI64Ty ra.ty = true
        · simp only [h64, ↓reduceIte, Option.some.injEq] at hLow
          subst hLow
          have s0 := op_const_sc tenvA ra.nextTmp 0#64
          let e1 := tenvA.bind (hloTmpReg ra.nextTmp) scUi64Ty
          have hra1 : e1 ra.reg = some scUi64Ty := by
            dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hA.2.2.1 _ (Nat.le_refl _))]; exact hA.2.2.2.2.1
          have s1 := op_sub e1 (ra.nextTmp + 1) (hloTmpReg ra.nextTmp) ra.reg scUi64Ty
            (canonicalSSAName_hloTmpReg _) hA.2.1 (typeEnv_bind_self _ _ _) hra1
          exact hloTyBlockPost_seq tenv k ra.nextTmp _ _ _ scUi64Ty scUi64Ty ra.ops _ hA
            (hloTyBlockPost_cons tenvA ra.nextTmp (ra.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
              (hloTyBlockPost_single e1 (ra.nextTmp + 1) _ _ s1.1 s1.2))
        · simp [h64] at hLow
  | binOp op lhs rhs ihL ihR =>
    dsimp [lowerScalarExpr] at hLow
    cases hL0 : lowerScalarExpr Γ lhs k with
    | none => simp [hL0] at hLow
    | some rl =>
      simp only [hL0, Option.bind] at hLow
      cases hR0 : lowerScalarExpr Γ rhs rl.nextTmp with
      | none => simp [hR0] at hLow
      | some rr =>
        simp only [hR0] at hLow
        have hL := ihL tenv k rl hWF hL0
        have hWFR := hloTypeEnvWF_frame Γ tenv (rl.ops.foldl bindResult tenv) k rl.nextTmp
          hWF hL.1 hL.2.2.2.2.2
        have hR := ihR (rl.ops.foldl bindResult tenv) rl.nextTmp rr hWFR hR0
        exact lowerHLOBinOpStep_canonical tenv k op rl rr rs hL hR hLow
  | select cond tv ev ihC ihT ihE =>
    dsimp [lowerScalarExpr] at hLow
    cases hC0 : lowerScalarExpr Γ cond k with
    | none => simp [hC0] at hLow
    | some rc =>
      simp only [hC0, Option.bind] at hLow
      cases hT0 : lowerScalarExpr Γ tv rc.nextTmp with
      | none => simp [hT0] at hLow
      | some rt =>
        simp only [hT0] at hLow
        cases hE0 : lowerScalarExpr Γ ev rt.nextTmp with
        | none => simp [hE0] at hLow
        | some re =>
          simp only [hE0] at hLow
          split at hLow
          · simp only [Option.some.injEq] at hLow
            subst hLow
            have hC := ihC tenv k rc hWF hC0
            let tenvC := rc.ops.foldl bindResult tenv
            have hWFT := hloTypeEnvWF_frame Γ tenv tenvC k rc.nextTmp hWF hC.1 hC.2.2.2.2.2
            have hT := ihT tenvC rc.nextTmp rt hWFT hT0
            let tenvT := rt.ops.foldl bindResult tenvC
            have hWFE := hloTypeEnvWF_frame Γ tenvC tenvT rc.nextTmp rt.nextTmp hWFT hT.1 hT.2.2.2.2.2
            have hE := ihE tenvT rt.nextTmp re hWFE hE0
            have hCT := hloTyBlockPost_seq tenv k rc.nextTmp rt.nextTmp rc.reg rt.reg scUi64Ty scUi64Ty
              rc.ops rt.ops hC (by simpa [tenvC] using hT)
            have hCTE := hloTyBlockPost_seq tenv k rt.nextTmp re.nextTmp rt.reg re.reg scUi64Ty scUi64Ty
              (rc.ops ++ rt.ops) re.ops hCT (by simpa [List.foldl_append, tenvC, tenvT] using hE)
            let tenvE := (rc.ops ++ rt.ops ++ re.ops).foldl bindResult tenv
            have hrcE : tenvE rc.reg = some scUi64Ty := by
              dsimp only [tenvE]
              rw [List.foldl_append, List.foldl_append]
              rw [show List.foldl bindResult (List.foldl bindResult tenv rc.ops) rt.ops = tenvT from rfl]
              rw [hE.2.2.2.2.2 rc.reg (fun j hj _ => hC.2.2.1 j (Nat.le_trans hT.1 hj))]
              dsimp only [tenvT]
              rw [hT.2.2.2.2.2 rc.reg (fun j hj _ => hC.2.2.1 j hj)]
              exact hC.2.2.2.2.1
            have hrtE : tenvE rt.reg = some scUi64Ty := by
              dsimp only [tenvE]
              rw [List.foldl_append, List.foldl_append,
                  hE.2.2.2.2.2 rt.reg (fun j hj _ => hT.2.2.1 j hj)]
              exact hT.2.2.2.2.1
            have hreE : tenvE re.reg = some scUi64Ty := by
              dsimp only [tenvE]; rw [List.foldl_append, List.foldl_append]; exact hE.2.2.2.2.1
            have s0 := op_convert tenvE re.nextTmp rc.reg scUi64Ty .i1 hC.2.1 hrcE
            let e1 := tenvE.bind (hloTmpReg re.nextTmp) scI1Ty
            have hrt1 : e1 rt.reg = some scUi64Ty := by
              dsimp only [e1]
              rw [typeEnv_bind_ne _ _ _ _ (hT.2.2.1 _ hE.1)]; exact hrtE
            have hre1 : e1 re.reg = some scUi64Ty := by
              dsimp only [e1]
              rw [typeEnv_bind_ne _ _ _ _ (hE.2.2.1 _ (Nat.le_refl _))]; exact hreE
            have s1 := op_select_sc e1 (re.nextTmp + 1) (hloTmpReg re.nextTmp) rt.reg re.reg
              (canonicalSSAName_hloTmpReg _) hT.2.1 hE.2.1 (typeEnv_bind_self _ _ _) hrt1 hre1
            exact hloTyBlockPost_seq tenv k re.nextTmp _ _ _ scUi64Ty scUi64Ty _ _ hCTE
              (hloTyBlockPost_cons tenvE re.nextTmp (re.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
                (hloTyBlockPost_single e1 (re.nextTmp + 1) _ _ s1.1 s1.2))
          · simp at hLow
  | fma a b c ihA ihB ihC =>
    dsimp [lowerScalarExpr] at hLow
    cases hA0 : lowerScalarExpr Γ a k with
    | none => simp [hA0] at hLow
    | some ra =>
      simp only [hA0, Option.bind] at hLow
      cases hB0 : lowerScalarExpr Γ b ra.nextTmp with
      | none => simp [hB0] at hLow
      | some rb =>
        simp only [hB0] at hLow
        cases hC0 : lowerScalarExpr Γ c rb.nextTmp with
        | none => simp [hC0] at hLow
        | some rc =>
          simp only [hC0] at hLow
          split at hLow
          · simp only [Option.some.injEq] at hLow
            subst hLow
            have hA := ihA tenv k ra hWF hA0
            let tenvA := ra.ops.foldl bindResult tenv
            have hWFB := hloTypeEnvWF_frame Γ tenv tenvA k ra.nextTmp hWF hA.1 hA.2.2.2.2.2
            have hB := ihB tenvA ra.nextTmp rb hWFB hB0
            let tenvB := rb.ops.foldl bindResult tenvA
            have hWFC := hloTypeEnvWF_frame Γ tenvA tenvB ra.nextTmp rb.nextTmp hWFB hB.1 hB.2.2.2.2.2
            have hC := ihC tenvB rb.nextTmp rc hWFC hC0
            have hAB := hloTyBlockPost_seq tenv k ra.nextTmp rb.nextTmp ra.reg rb.reg scUi64Ty scUi64Ty
              ra.ops rb.ops hA (by simpa [tenvA] using hB)
            have hABC := hloTyBlockPost_seq tenv k rb.nextTmp rc.nextTmp rb.reg rc.reg scUi64Ty scUi64Ty
              (ra.ops ++ rb.ops) rc.ops hAB (by simpa [List.foldl_append, tenvA, tenvB] using hC)
            let tenvC := (ra.ops ++ rb.ops ++ rc.ops).foldl bindResult tenv
            have hraC : tenvC ra.reg = some scUi64Ty := by
              dsimp only [tenvC]
              rw [List.foldl_append, List.foldl_append]
              rw [show List.foldl bindResult (List.foldl bindResult tenv ra.ops) rb.ops = tenvB from rfl]
              rw [hC.2.2.2.2.2 ra.reg (fun j hj _ => hA.2.2.1 j (Nat.le_trans hB.1 hj))]
              dsimp only [tenvB]
              rw [hB.2.2.2.2.2 ra.reg (fun j hj _ => hA.2.2.1 j hj)]
              exact hA.2.2.2.2.1
            have hrbC : tenvC rb.reg = some scUi64Ty := by
              dsimp only [tenvC]
              rw [List.foldl_append, List.foldl_append,
                  hC.2.2.2.2.2 rb.reg (fun j hj _ => hB.2.2.1 j hj)]
              exact hB.2.2.2.2.1
            have hrcC : tenvC rc.reg = some scUi64Ty := by
              dsimp only [tenvC]; rw [List.foldl_append, List.foldl_append]; exact hC.2.2.2.2.1
            have s0 := op_mul tenvC rc.nextTmp ra.reg rb.reg scUi64Ty hA.2.1 hB.2.1 hraC hrbC
            let e1 := tenvC.bind (hloTmpReg rc.nextTmp) scUi64Ty
            have hrc1 : e1 rc.reg = some scUi64Ty := by
              dsimp only [e1]
              rw [typeEnv_bind_ne _ _ _ _ (hC.2.2.1 _ (Nat.le_refl _))]; exact hrcC
            have s1 := op_add e1 (rc.nextTmp + 1) (hloTmpReg rc.nextTmp) rc.reg scUi64Ty
              (canonicalSSAName_hloTmpReg _) hC.2.1 (typeEnv_bind_self _ _ _) hrc1
            exact hloTyBlockPost_seq tenv k rc.nextTmp _ _ _ scUi64Ty scUi64Ty _ _ hABC
              (hloTyBlockPost_cons tenvC rc.nextTmp (rc.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
                (hloTyBlockPost_single e1 (rc.nextTmp + 1) _ _ s1.1 s1.2))
          · simp at hLow

private theorem lowerScalarCode_canonical (Γ : HLOTyEnv) (code : LNIRCode) (tenv : TypeEnv)
    (k : Nat) (rs : HLOScalarRes)
    (hWF : HLOTypeEnvWF Γ tenv k)
    (hLow : lowerScalarCode Γ code k = some rs) :
    HLOTyBlockPost tenv k rs.nextTmp rs.reg scUi64Ty rs.ops := by
  induction code generalizing Γ tenv k rs with
  | ret v =>
    dsimp [lowerScalarCode] at hLow
    cases hΓ : Γ v with
    | none => simp [hΓ] at hLow
    | some entry =>
      rcases entry with ⟨r, vk⟩
      cases vk with
      | tensor1D _ => simp [hΓ] at hLow
      | scalar ty kn =>
        simp only [hΓ] at hLow
        split at hLow
        · simp only [Option.some.injEq] at hLow
          subst hLow
          obtain ⟨hr, hty, hfr⟩ := hWF v ⟨r, .scalar ty kn⟩ hΓ
          exact hloTyBlockPost_nil tenv k r scUi64Ty hr hfr hty
        · simp at hLow
  | letBind dst declTy rhs kCode ih =>
    cases rhs with
    | scalar se =>
      dsimp [lowerScalarCode] at hLow
      cases hS0 : lowerScalarExpr Γ se k with
      | none => simp [hS0] at hLow
      | some rse =>
        simp only [hS0, Option.bind] at hLow
        split at hLow
        · cases hK0 : lowerScalarCode (Γ.bind dst ⟨rse.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
              kCode rse.nextTmp with
          | none => simp [hK0] at hLow
          | some rk =>
            simp only [hK0, Option.some.injEq] at hLow
            subst hLow
            have hS := lowerScalarExpr_canonical Γ se tenv k rse hWF hS0
            let tenvS := rse.ops.foldl bindResult tenv
            have hWFS := hloTypeEnvWF_frame Γ tenv tenvS k rse.nextTmp hWF hS.1 hS.2.2.2.2.2
            have hWFB := hloTypeEnvWF_bind Γ tenvS rse.nextTmp dst rse.reg
              (.scalar declTy (knownNatOfScalarExpr se)) hWFS hS.2.1 hS.2.2.2.2.1 hS.2.2.1
            have hK := ih _ tenvS rse.nextTmp rk hWFB hK0
            exact hloTyBlockPost_seq tenv k rse.nextTmp rk.nextTmp rse.reg rk.reg scUi64Ty scUi64Ty
              rse.ops rk.ops hS hK
        · simp at hLow
    | _ => simp [lowerScalarCode] at hLow
  | ite condVar thenB elseB ihT ihE =>
    dsimp [lowerScalarCode] at hLow
    cases hΓc : Γ condVar with
    | none => simp [hΓc] at hLow
    | some ec =>
      rcases ec with ⟨cReg, vkc⟩
      cases vkc with
      | tensor1D _ => simp [hΓc] at hLow
      | scalar cTy knc =>
        simp only [hΓc] at hLow
        split at hLow
        · cases hT0 : lowerScalarCode Γ thenB k with
          | none => simp [hT0, Option.bind] at hLow
          | some rt =>
            simp only [hT0, Option.bind] at hLow
            cases hE0 : lowerScalarCode Γ elseB rt.nextTmp with
            | none => simp [hE0] at hLow
            | some re =>
              simp only [hE0] at hLow
              split at hLow
              · simp only [Option.some.injEq] at hLow
                subst hLow
                obtain ⟨hcName, hcTy, hcFr⟩ := hWF condVar ⟨cReg, .scalar cTy knc⟩ hΓc
                have hT := ihT Γ tenv k rt hWF hT0
                let tenvT := rt.ops.foldl bindResult tenv
                have hWFE := hloTypeEnvWF_frame Γ tenv tenvT k rt.nextTmp hWF hT.1 hT.2.2.2.2.2
                have hE := ihE Γ tenvT rt.nextTmp re hWFE hE0
                have hTE := hloTyBlockPost_seq tenv k rt.nextTmp re.nextTmp rt.reg re.reg scUi64Ty scUi64Ty
                  rt.ops re.ops hT hE
                let tenvE := (rt.ops ++ re.ops).foldl bindResult tenv
                have hcE : tenvE cReg = some scUi64Ty := by
                  dsimp only [tenvE]
                  rw [hTE.2.2.2.2.2 cReg (fun j hj _ => hcFr j hj)]
                  exact hcTy
                have hrtE : tenvE rt.reg = some scUi64Ty := by
                  dsimp only [tenvE]
                  rw [List.foldl_append, hE.2.2.2.2.2 rt.reg (fun j hj _ => hT.2.2.1 j hj)]
                  exact hT.2.2.2.2.1
                have hreE : tenvE re.reg = some scUi64Ty := by
                  dsimp only [tenvE]; rw [List.foldl_append]; exact hE.2.2.2.2.1
                have s0 := op_convert tenvE re.nextTmp cReg scUi64Ty .i1 hcName hcE
                let e1 := tenvE.bind (hloTmpReg re.nextTmp) scI1Ty
                have hrt1 : e1 rt.reg = some scUi64Ty := by
                  dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hT.2.2.1 _ hE.1)]; exact hrtE
                have hre1 : e1 re.reg = some scUi64Ty := by
                  dsimp only [e1]; rw [typeEnv_bind_ne _ _ _ _ (hE.2.2.1 _ (Nat.le_refl _))]; exact hreE
                have s1 := op_select_sc e1 (re.nextTmp + 1) (hloTmpReg re.nextTmp) rt.reg re.reg
                  (canonicalSSAName_hloTmpReg _) hT.2.1 hE.2.1 (typeEnv_bind_self _ _ _) hrt1 hre1
                exact hloTyBlockPost_seq tenv k re.nextTmp _ _ _ scUi64Ty scUi64Ty _ _ hTE
                  (hloTyBlockPost_cons tenvE re.nextTmp (re.nextTmp + 2) _ _ _ _ _ s0.1 s0.2
                    (hloTyBlockPost_single e1 (re.nextTmp + 1) _ _ s1.1 s1.2))
              · simp at hLow
        · simp at hLow
  | _ => simp [lowerScalarCode] at hLow

private theorem lowerParKernel_canonical (Γ : HLOTyEnv) (lenVar : VarId) (inputs : List VarId)
    (kernel : ParallelKernelKind) (tenv : TypeEnv) (k : Nat) (res : HLOCodeRes)
    (hWF : HLOTypeEnvWF Γ tenv k)
    (hLow : lowerParKernel Γ lenVar inputs kernel k = some res) :
    HLOTyBlockPost tenv k res.nextTmp res.reg res.outKind.tensorType res.ops := by
  dsimp [lowerParKernel] at hLow
  cases hΓL : Γ lenVar with
  | none => simp [hΓL] at hLow
  | some eL =>
    rcases eL with ⟨rLen, vkL⟩
    cases vkL with
    | tensor1D _ => simp [hΓL] at hLow
    | scalar tyL knL =>
      cases tyL <;> try (simp [hΓL] at hLow; done)
      cases knL with
      | none => simp [hΓL] at hLow
      | some n =>
        simp only [hΓL] at hLow
        cases kernel with
        | stencil1D3Pt _ _ _ => simp at hLow
        | customScalar _ _ _ => simp at hLow
        | mapScaleAdd scale bias =>
          rcases inputs with _ | ⟨x, _ | _⟩ <;> try (simp at hLow; done)
          cases hΓx : Γ x with
          | none => simp [hΓx] at hLow
          | some ex =>
            rcases ex with ⟨rx, vkx⟩
            cases vkx with
            | scalar _ _ => simp [hΓx] at hLow
            | tensor1D nx =>
              simp only [hΓx] at hLow
              by_cases hnx : (nx == n) = true
              · simp only [hnx, ↓reduceIte, Option.some.injEq] at hLow
                have hnx_eq : nx = n := eq_of_beq hnx
                subst nx
                subst hLow
                obtain ⟨hrx, htyx, hfrx⟩ := hWF x ⟨rx, .tensor1D n⟩ hΓx
                let e1 := tenv.bind (hloTmpReg k) scUi64Ty
                let e2 := e1.bind (hloTmpReg (k + 1)) (vecUi64Ty n)
                let e3 := e2.bind (hloTmpReg (k + 2)) (vecUi64Ty n)
                let e4 := e3.bind (hloTmpReg (k + 3)) scUi64Ty
                let e5 := e4.bind (hloTmpReg (k + 4)) (vecUi64Ty n)
                have hrx2 : e2 rx = some (vecUi64Ty n) := by
                  dsimp only [e2, e1]
                  rw [typeEnv_bind_ne _ _ _ _ (hfrx (k + 1) (by omega)),
                      typeEnv_bind_ne _ _ _ _ (hfrx k (by omega))]
                  exact htyx
                have hm5 : e5 (hloTmpReg (k + 2)) = some (vecUi64Ty n) := by
                  dsimp only [e5, e4, e3]
                  rw [typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
                      typeEnv_bind_ne _ _ _ _ (hloTmpReg_ne_of_ne (by omega)),
                      typeEnv_bind_self]
                have s0 := op_const_sc tenv k scale.toBitVec
                have s1 := op_broadcast_sc e1 (k + 1) n (hloTmpReg k)
                  (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                have s2 := op_mul e2 (k + 2) rx (hloTmpReg (k + 1)) (vecUi64Ty n)
                  hrx (canonicalSSAName_hloTmpReg _) hrx2 (typeEnv_bind_self _ _ _)
                have s3 := op_const_sc e3 (k + 3) bias.toBitVec
                have s4 := op_broadcast_sc e4 (k + 4) n (hloTmpReg (k + 3))
                  (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                have s5 := op_add e5 (k + 5) (hloTmpReg (k + 2)) (hloTmpReg (k + 4)) (vecUi64Ty n)
                  (canonicalSSAName_hloTmpReg _) (canonicalSSAName_hloTmpReg _) hm5 (typeEnv_bind_self _ _ _)
                exact hloTyBlockPost_cons tenv k (k + 6) _ _ _ _ _ s0.1 s0.2
                  (hloTyBlockPost_cons e1 (k + 1) (k + 6) _ _ _ _ _ s1.1 s1.2
                    (hloTyBlockPost_cons e2 (k + 2) (k + 6) _ _ _ _ _ s2.1 s2.2
                      (hloTyBlockPost_cons e3 (k + 3) (k + 6) _ _ _ _ _ s3.1 s3.2
                        (hloTyBlockPost_cons e4 (k + 4) (k + 6) _ _ _ _ _ s4.1 s4.2
                          (hloTyBlockPost_single e5 (k + 5) _ _ s5.1 s5.2)))))
              · simp [hnx] at hLow
        | zipAdd =>
          rcases inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> try (simp at hLow; done)
          cases hΓx : Γ x with
          | none => simp [hΓx] at hLow
          | some ex =>
            rcases ex with ⟨rx, vkx⟩
            cases vkx with
            | scalar _ _ => simp [hΓx] at hLow
            | tensor1D nx =>
              cases hΓy : Γ y with
              | none => simp [hΓx, hΓy] at hLow
              | some ey =>
                rcases ey with ⟨ry, vky⟩
                cases vky with
                | scalar _ _ => simp [hΓx, hΓy] at hLow
                | tensor1D ny =>
                  simp only [hΓx, hΓy] at hLow
                  by_cases hxy : (nx == n && ny == n) = true
                  · simp only [hxy, ↓reduceIte, Option.some.injEq] at hLow
                    rcases Bool.and_eq_true_iff.mp hxy with ⟨hnx, hny⟩
                    have hnx_eq := eq_of_beq hnx; have hny_eq := eq_of_beq hny
                    subst nx; subst ny; subst hLow
                    obtain ⟨hrx, htyx, _⟩ := hWF x ⟨rx, .tensor1D n⟩ hΓx
                    obtain ⟨hry, htyy, _⟩ := hWF y ⟨ry, .tensor1D n⟩ hΓy
                    have s := op_add tenv k rx ry (vecUi64Ty n) hrx hry htyx htyy
                    exact hloTyBlockPost_single tenv k _ _ s.1 s.2
                  · simp [hxy] at hLow
        | zipMul =>
          rcases inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> try (simp at hLow; done)
          cases hΓx : Γ x with
          | none => simp [hΓx] at hLow
          | some ex =>
            rcases ex with ⟨rx, vkx⟩
            cases vkx with
            | scalar _ _ => simp [hΓx] at hLow
            | tensor1D nx =>
              cases hΓy : Γ y with
              | none => simp [hΓx, hΓy] at hLow
              | some ey =>
                rcases ey with ⟨ry, vky⟩
                cases vky with
                | scalar _ _ => simp [hΓx, hΓy] at hLow
                | tensor1D ny =>
                  simp only [hΓx, hΓy] at hLow
                  by_cases hxy : (nx == n && ny == n) = true
                  · simp only [hxy, ↓reduceIte, Option.some.injEq] at hLow
                    rcases Bool.and_eq_true_iff.mp hxy with ⟨hnx, hny⟩
                    have hnx_eq := eq_of_beq hnx; have hny_eq := eq_of_beq hny
                    subst nx; subst ny; subst hLow
                    obtain ⟨hrx, htyx, _⟩ := hWF x ⟨rx, .tensor1D n⟩ hΓx
                    obtain ⟨hry, htyy, _⟩ := hWF y ⟨ry, .tensor1D n⟩ hΓy
                    have s := op_mul tenv k rx ry (vecUi64Ty n) hrx hry htyx htyy
                    exact hloTyBlockPost_single tenv k _ _ s.1 s.2
                  · simp [hxy] at hLow
        | saxpy alpha =>
          rcases inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> try (simp at hLow; done)
          cases hΓx : Γ x with
          | none => simp [hΓx] at hLow
          | some ex =>
            rcases ex with ⟨rx, vkx⟩
            cases vkx with
            | scalar _ _ => simp [hΓx] at hLow
            | tensor1D nx =>
              cases hΓy : Γ y with
              | none => simp [hΓx, hΓy] at hLow
              | some ey =>
                rcases ey with ⟨ry, vky⟩
                cases vky with
                | scalar _ _ => simp [hΓx, hΓy] at hLow
                | tensor1D ny =>
                  simp only [hΓx, hΓy] at hLow
                  by_cases hxy : (nx == n && ny == n) = true
                  · simp only [hxy, ↓reduceIte, Option.some.injEq] at hLow
                    rcases Bool.and_eq_true_iff.mp hxy with ⟨hnx, hny⟩
                    have hnx_eq := eq_of_beq hnx; have hny_eq := eq_of_beq hny
                    subst nx; subst ny; subst hLow
                    obtain ⟨hrx, htyx, hfrx⟩ := hWF x ⟨rx, .tensor1D n⟩ hΓx
                    obtain ⟨hry, htyy, hfry⟩ := hWF y ⟨ry, .tensor1D n⟩ hΓy
                    let e1 := tenv.bind (hloTmpReg k) scUi64Ty
                    let e2 := e1.bind (hloTmpReg (k + 1)) (vecUi64Ty n)
                    let e3 := e2.bind (hloTmpReg (k + 2)) (vecUi64Ty n)
                    have hrx2 : e2 rx = some (vecUi64Ty n) := by
                      dsimp only [e2, e1]
                      rw [typeEnv_bind_ne _ _ _ _ (hfrx (k + 1) (by omega)),
                          typeEnv_bind_ne _ _ _ _ (hfrx k (by omega))]
                      exact htyx
                    have hry3 : e3 ry = some (vecUi64Ty n) := by
                      dsimp only [e3, e2, e1]
                      rw [typeEnv_bind_ne _ _ _ _ (hfry (k + 2) (by omega)),
                          typeEnv_bind_ne _ _ _ _ (hfry (k + 1) (by omega)),
                          typeEnv_bind_ne _ _ _ _ (hfry k (by omega))]
                      exact htyy
                    have s0 := op_const_sc tenv k alpha.toBitVec
                    have s1 := op_broadcast_sc e1 (k + 1) n (hloTmpReg k)
                      (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                    have s2 := op_mul e2 (k + 2) (hloTmpReg (k + 1)) rx (vecUi64Ty n)
                      (canonicalSSAName_hloTmpReg _) hrx (typeEnv_bind_self _ _ _) hrx2
                    have s3 := op_add e3 (k + 3) (hloTmpReg (k + 2)) ry (vecUi64Ty n)
                      (canonicalSSAName_hloTmpReg _) hry (typeEnv_bind_self _ _ _) hry3
                    exact hloTyBlockPost_cons tenv k (k + 4) _ _ _ _ _ s0.1 s0.2
                      (hloTyBlockPost_cons e1 (k + 1) (k + 4) _ _ _ _ _ s1.1 s1.2
                        (hloTyBlockPost_cons e2 (k + 2) (k + 4) _ _ _ _ _ s2.1 s2.2
                          (hloTyBlockPost_single e3 (k + 3) _ _ s3.1 s3.2)))
                  · simp [hxy] at hLow
        | dotProduct =>
          rcases inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> try (simp at hLow; done)
          cases hΓx : Γ x with
          | none => simp [hΓx] at hLow
          | some ex =>
            rcases ex with ⟨rx, vkx⟩
            cases vkx with
            | scalar _ _ => simp [hΓx] at hLow
            | tensor1D nx =>
              cases hΓy : Γ y with
              | none => simp [hΓx, hΓy] at hLow
              | some ey =>
                rcases ey with ⟨ry, vky⟩
                cases vky with
                | scalar _ _ => simp [hΓx, hΓy] at hLow
                | tensor1D ny =>
                  simp only [hΓx, hΓy] at hLow
                  by_cases hxy : (nx == n && ny == n) = true
                  · simp only [hxy, ↓reduceIte, Option.some.injEq] at hLow
                    rcases Bool.and_eq_true_iff.mp hxy with ⟨hnx, hny⟩
                    have hnx_eq := eq_of_beq hnx; have hny_eq := eq_of_beq hny
                    subst nx; subst ny; subst hLow
                    obtain ⟨hrx, htyx, _⟩ := hWF x ⟨rx, .tensor1D n⟩ hΓx
                    obtain ⟨hry, htyy, _⟩ := hWF y ⟨ry, .tensor1D n⟩ hΓy
                    let e1 := tenv.bind (hloTmpReg k) scUi64Ty
                    have s0 := op_dot_1d tenv k n rx ry hrx hry htyx htyy
                    have s1 := op_reshape_sc_to_vec1 e1 (k + 1) (hloTmpReg k)
                      (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                    exact hloTyBlockPost_cons tenv k (k + 2) _ _ _ _ _ s0.1 s0.2
                      (hloTyBlockPost_single e1 (k + 1) _ _ s1.1 s1.2)
                  · simp [hxy] at hLow

private theorem lowerCode_canonical (Γ : HLOTyEnv) (code : LNIRCode) (tenv : TypeEnv)
    (k : Nat) (rc : HLOCodeRes)
    (hWF : HLOTypeEnvWF Γ tenv k)
    (hLow : lowerCode Γ code k = some rc) :
    HLOTyBlockPost tenv k rc.nextTmp rc.reg rc.outKind.tensorType rc.ops := by
  induction code generalizing Γ tenv k rc with
  | ret v =>
    dsimp [lowerCode] at hLow
    cases hΓ : Γ v with
    | none => simp [hΓ] at hLow
    | some entry =>
      rcases entry with ⟨r, vk⟩
      cases vk with
      | tensor1D n =>
        simp only [hΓ, Option.some.injEq] at hLow
        subst hLow
        obtain ⟨hr, hty, hfr⟩ := hWF v ⟨r, .tensor1D n⟩ hΓ
        exact hloTyBlockPost_nil tenv k r (vecUi64Ty n) hr hfr hty
      | scalar ty kn =>
        simp only [hΓ] at hLow
        split at hLow
        · simp only [Option.some.injEq] at hLow
          subst hLow
          obtain ⟨hr, hty, hfr⟩ := hWF v ⟨r, .scalar ty kn⟩ hΓ
          exact hloTyBlockPost_nil tenv k r scUi64Ty hr hfr hty
        · simp at hLow
  | letBind dst declTy rhs kCode ih =>
    cases rhs with
    | scalar se =>
      dsimp [lowerCode] at hLow
      cases hS0 : lowerScalarExpr Γ se k with
      | none => simp [hS0] at hLow
      | some rs =>
        simp only [hS0, Option.bind] at hLow
        split at hLow
        · cases hK0 : lowerCode (Γ.bind dst ⟨rs.reg, .scalar declTy (knownNatOfScalarExpr se)⟩)
              kCode rs.nextTmp with
          | none => simp [hK0] at hLow
          | some rk =>
            simp only [hK0, Option.some.injEq] at hLow
            subst hLow
            have hS := lowerScalarExpr_canonical Γ se tenv k rs hWF hS0
            let tenvS := rs.ops.foldl bindResult tenv
            have hWFS := hloTypeEnvWF_frame Γ tenv tenvS k rs.nextTmp hWF hS.1 hS.2.2.2.2.2
            have hWFB := hloTypeEnvWF_bind Γ tenvS rs.nextTmp dst rs.reg
              (.scalar declTy (knownNatOfScalarExpr se)) hWFS hS.2.1 hS.2.2.2.2.1 hS.2.2.1
            have hK := ih _ tenvS rs.nextTmp rk hWFB hK0
            exact hloTyBlockPost_seq tenv k rs.nextTmp rk.nextTmp rs.reg rk.reg
              scUi64Ty rk.outKind.tensorType rs.ops rk.ops hS hK
        · simp at hLow
    | sarrayLen arrVar =>
      cases declTy <;> try (simp [lowerCode] at hLow; done)
      case i64 =>
        dsimp [lowerCode] at hLow
        cases hΓA : Γ arrVar with
        | none => simp [hΓA] at hLow
        | some eA =>
          rcases eA with ⟨rArr, vkA⟩
          cases vkA with
          | scalar _ _ => simp [hΓA] at hLow
          | tensor1D n =>
            simp only [hΓA] at hLow
            split at hLow
            · cases hK0 : lowerCode (Γ.bind dst ⟨hloTmpReg k, .scalar .i64 (some n)⟩) kCode (k + 1) with
              | none => simp [hK0, Option.bind] at hLow
              | some rk =>
                simp only [hK0, Option.bind, Option.some.injEq] at hLow
                subst hLow
                have s0 := op_const_sc tenv k (BitVec.ofNat 64 n)
                let e1 := tenv.bind (hloTmpReg k) scUi64Ty
                have hWF1 := hloTypeEnvWF_frame Γ tenv e1 k (k + 1) hWF (Nat.le_succ k)
                  (fun q hq => typeEnv_bind_ne _ _ _ _ (hq k (Nat.le_refl k) (Nat.lt_succ_self k)))
                have hWFB := hloTypeEnvWF_bind Γ e1 (k + 1) dst (hloTmpReg k) (.scalar .i64 (some n))
                  hWF1 (canonicalSSAName_hloTmpReg k) (typeEnv_bind_self _ _ _)
                  (fun j hj => hloTmpReg_ne_of_ne (by omega))
                have hK := ih _ e1 (k + 1) rk hWFB hK0
                exact hloTyBlockPost_cons tenv k rk.nextTmp _ _ _ _ _ s0.1 s0.2 hK
            · simp at hLow
    | sarrayGet arrVar idxVar elemTy =>
      cases declTy <;> try (simp [lowerCode] at hLow; done)
      case i64 =>
        cases elemTy <;> try (simp [lowerCode] at hLow; done)
        case i64 =>
          dsimp [lowerCode] at hLow
          cases hΓA : Γ arrVar with
          | none => simp [hΓA] at hLow
          | some eA =>
            rcases eA with ⟨rArr, vkA⟩
            cases vkA with
            | scalar _ _ => simp [hΓA] at hLow
            | tensor1D n =>
              cases hΓI : Γ idxVar with
              | none => simp [hΓA, hΓI] at hLow
              | some eI =>
                rcases eI with ⟨rIdx, vkI⟩
                cases vkI with
                | tensor1D _ => simp [hΓA, hΓI] at hLow
                | scalar tyI knI =>
                  cases tyI <;> try (simp [hΓA, hΓI] at hLow; done)
                  cases knI with
                  | none => simp [hΓA, hΓI] at hLow
                  | some idx =>
                    simp only [hΓA, hΓI] at hLow
                    by_cases hlt : decide (idx < n) = true
                    · simp only [hlt, ↓reduceIte] at hLow
                      have hIdxLt : idx < n := of_decide_eq_true hlt
                      cases hK0 : lowerCode (Γ.bind dst ⟨hloTmpReg (k + 1), .scalar .i64 none⟩) kCode (k + 2) with
                      | none => simp [hK0, Option.bind] at hLow
                      | some rk =>
                        simp only [hK0, Option.bind, Option.some.injEq] at hLow
                        subst hLow
                        obtain ⟨hrArr, htyArr, _⟩ := hWF arrVar ⟨rArr, .tensor1D n⟩ hΓA
                        let e1 := tenv.bind (hloTmpReg k) (vecUi64Ty 1)
                        let e2 := e1.bind (hloTmpReg (k + 1)) scUi64Ty
                        have s0 := op_slice_one tenv k n idx rArr hrArr htyArr hIdxLt
                        have s1 := op_reshape_vec1_to_sc e1 (k + 1) (hloTmpReg k)
                          (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                        have hOps0 : HLOTyBlockPost tenv k (k + 2) (hloTmpReg (k + 1)) scUi64Ty
                            [ .slice (hloTmpReg k) rArr [idx] [idx + 1] [1]
                            , .reshape (hloTmpReg (k + 1)) (hloTmpReg k) [] ] :=
                          hloTyBlockPost_cons tenv k (k + 2) _ _ _ _ _ s0.1 s0.2
                            (hloTyBlockPost_single e1 (k + 1) _ _ s1.1 s1.2)
                        have hFold0 : ([ StableHLOOp.slice (hloTmpReg k) rArr [idx] [idx + 1] [1]
                                       , StableHLOOp.reshape (hloTmpReg (k + 1)) (hloTmpReg k) [] ].foldl
                                       bindResult tenv) = e2 := by
                          simp [List.foldl_cons, s0.2, s1.2, e1, e2]
                        have hWF2 := hloTypeEnvWF_frame Γ tenv e2 k (k + 2) hWF hOps0.1
                          (by rw [← hFold0]; exact hOps0.2.2.2.2.2)
                        have hWFB := hloTypeEnvWF_bind Γ e2 (k + 2) dst (hloTmpReg (k + 1)) (.scalar .i64 none)
                          hWF2 (canonicalSSAName_hloTmpReg _) (typeEnv_bind_self _ _ _)
                          (fun j hj => hloTmpReg_ne_of_ne (by omega))
                        have hK := ih _ e2 (k + 2) rk hWFB hK0
                        exact hloTyBlockPost_seq tenv k (k + 2) rk.nextTmp _ rk.reg
                          scUi64Ty rk.outKind.tensorType _ rk.ops hOps0 (by rwa [hFold0])
                    · simp [hlt] at hLow
    | _ => simp [lowerCode] at hLow
  | parFor outVar lenVar inputs elemTy kernel kCode ih =>
    cases elemTy <;> try (simp [lowerCode] at hLow; done)
    case i64 =>
      dsimp [lowerCode] at hLow
      cases hP0 : lowerParKernel Γ lenVar inputs kernel k with
      | none => simp [hP0] at hLow
      | some rp =>
        simp only [hP0, Option.bind] at hLow
        cases hK0 : lowerCode (Γ.bind outVar ⟨rp.reg, rp.outKind⟩) kCode rp.nextTmp with
        | none => simp [hK0] at hLow
        | some rk =>
          simp only [hK0, Option.some.injEq] at hLow
          subst hLow
          have hP := lowerParKernel_canonical Γ lenVar inputs kernel tenv k rp hWF hP0
          let tenvP := rp.ops.foldl bindResult tenv
          have hWFP := hloTypeEnvWF_frame Γ tenv tenvP k rp.nextTmp hWF hP.1 hP.2.2.2.2.2
          have hWFB := hloTypeEnvWF_bind Γ tenvP rp.nextTmp outVar rp.reg rp.outKind
            hWFP hP.2.1 hP.2.2.2.2.1 hP.2.2.1
          have hK := ih _ tenvP rp.nextTmp rk hWFB hK0
          exact hloTyBlockPost_seq tenv k rp.nextTmp rk.nextTmp rp.reg rk.reg
            rp.outKind.tensorType rk.outKind.tensorType rp.ops rk.ops hP hK
  | ite condVar thenB elseB _ _ =>
    dsimp [lowerCode] at hLow
    cases hS0 : lowerScalarCode Γ (.ite condVar thenB elseB) k with
    | none => simp [hS0] at hLow
    | some rs =>
      simp only [hS0, Option.bind, Option.some.injEq] at hLow
      subst hLow
      exact lowerScalarCode_canonical Γ (.ite condVar thenB elseB) tenv k rs hWF hS0
  | _ => simp [lowerCode] at hLow

/-- Every `FuncOp` produced by `StableHLOLower.lowerToStableHLO` on a declaration with a
canonical SSA function name satisfies `CanonicalFuncOp` (purely syntactic/type-well-formed). -/
theorem lowerToStableHLO_canonical (d : LNIRDecl) (tensorLen : Nat) (fn : FuncOp)
    (hn : CanonicalSSAName d.name)
    (hLower : lowerToStableHLO d tensorLen = some fn) :
    CanonicalFuncOp fn := by
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
        obtain ⟨hParams, hWF0⟩ := initHLOParamsAcc_canonical tensorLen HLOTyEnv.empty TypeEnv.empty
          d.params (Γ0, params) (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) hInit
        let tenv0 := params.foldl (fun e (n, ty) => e.bind n ty) TypeEnv.empty
        have hCode := lowerCode_canonical Γ0 d.body tenv0 0 rc hWF0 hLow
        refine ⟨hn, hParams, ?_⟩
        rw [CanonicalBody.append]
        refine ⟨hCode.2.2.2.1, ?_⟩
        dsimp only [CanonicalBody, CanonicalStableHLOOp]
        exact ⟨⟨hCode.2.1, by simp [tenv0, hCode.2.2.2.2.1]⟩, trivial⟩

/-- Every `FuncOp` produced by `StableHLOLower.lowerToStableHLO` on a declaration with a
canonical SSA function name roundtrips through `parseFuncOp ∘ ppFuncOp`. -/
theorem lowerToStableHLO_roundtrip (d : LNIRDecl) (tensorLen : Nat) (fn : FuncOp)
    (hn : CanonicalSSAName d.name)
    (hLower : lowerToStableHLO d tensorLen = some fn) :
    parseFuncOp (ppFuncOp fn) = some fn :=
  parseFuncOp_roundtrip fn (lowerToStableHLO_canonical d tensorLen fn hn hLower)


end LeanNative.Proofs
