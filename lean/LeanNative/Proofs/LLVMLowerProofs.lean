import LeanNative.Proofs.LLVMCFGLowerProofs

/-!
# Top-Level `LNIR → LLVMAst` Soundness & Mutant Kills (`LeanNative.Proofs.LLVMLowerProofs`)

Proves end-to-end semantic preservation (`lowerToLLVM_sound`) from `LNIRDecl`
(`LeanNative.Semantics.evalCode`) to `LLVMFn` / `LLVMModule`
(`LeanNative.Backend.LLVMAst.execFn`), non-vacuity (`lowerToLLVM_nonvacuous`),
and semantic mutant kills (`mutant_m1_killed`..`mutant_m5_killed`).
-/

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

/-! ## 1. Parameter Binding & Top-Level `lowerToLLVM_sound` -/

/-- Bind a list of `LNIRParam`s to source `Val`s left-to-right, matching `LLVMAst.bindArgs`. -/
def bindParamEnv (env : VarEnv) : List LNIRParam → List Val → VarEnv
  | [], _ => env
  | _, [] => env
  | p :: ps, v :: vs => bindParamEnv (env.bind p.id v) ps vs

/-- Encode typed source argument `Val`s as `i64`-word `LLVMVal`s matching `d.params`. -/
def encodeParamArgs : List LNIRParam → List Val → Option (List LLVMVal)
  | [], [] => some []
  | p :: ps, v :: vs => do
    let w ← encodeScalarTyped p.ty v
    let ws ← encodeParamArgs ps vs
    some (.bits .i64 w :: ws)
  | _, _ => none

theorem empty_envTypedAgree :
    EnvTypedAgree ScalarTyEnv.empty VarEnv.empty ([] : List (RegName × LLVMVal)) := by
  intro x ty h
  cases h

theorem bindParams_post (Γ : ScalarTyEnv) (env : VarEnv) (st : ExecState)
    (ps : List LNIRParam) (vs : List Val) (Γ' : ScalarTyEnv) (llvmArgs : List LLVMVal)
    (hAgree : EnvTypedAgree Γ env st.regs)
    (hTy : initParamTyEnvAcc Γ ps = some Γ')
    (hArgs : encodeParamArgs ps vs = some llvmArgs) :
    ∃ st',
      bindArgs st (ps.map fun p => ⟨varReg p.id, w64, []⟩) llvmArgs = some st' ∧
      st'.mem = st.mem ∧
      st'.globals = st.globals ∧
      EnvTypedAgree Γ' (bindParamEnv env ps vs) st'.regs := by
  induction ps generalizing Γ env st vs llvmArgs with
  | nil =>
    cases vs with
    | nil =>
      simp only [initParamTyEnvAcc, Option.some.injEq] at hTy
      simp only [encodeParamArgs, Option.some.injEq] at hArgs
      subst hTy
      subst hArgs
      exact ⟨st, rfl, rfl, rfl, hAgree⟩
    | cons _ _ =>
      simp [encodeParamArgs] at hArgs
  | cons p ps' ih =>
    cases vs with
    | nil =>
      simp [encodeParamArgs] at hArgs
    | cons v vs' =>
      dsimp [encodeParamArgs] at hArgs
      cases hw : encodeScalarTyped p.ty v with
      | none => simp [hw] at hArgs
      | some w =>
        simp only [hw, Option.bind] at hArgs
        cases hws : encodeParamArgs ps' vs' with
        | none => simp [hws] at hArgs
        | some ws =>
          simp only [hws, Option.some.injEq] at hArgs
          subst hArgs
          dsimp [initParamTyEnvAcc] at hTy
          by_cases h64 : isI64Ty p.ty = true
          · simp only [h64, ↓reduceIte] at hTy
            have hp : p.ty = .i64 := isI64Ty_eq_true p.ty h64
            rw [hp] at hw
            have hAg1 : EnvTypedAgree (Γ.bind p.id .i64) (env.bind p.id v)
                (bindReg st (varReg p.id) (.bits .i64 w)).regs :=
              envTypedAgree_bind_var Γ env st.regs p.id .i64 v w hAgree hw
            rcases ih (Γ.bind p.id .i64) (env.bind p.id v)
              (bindReg st (varReg p.id) (.bits .i64 w)) vs' ws hAg1 hTy hws with
              ⟨st', hBind, hMem, hGlob, hAg'⟩
            exact ⟨st', hBind, hMem, hGlob, hAg'⟩
          · simp only [h64, Bool.false_eq_true, ↓reduceIte] at hTy
            by_cases h1 : isI1Ty p.ty = true
            · simp only [h1, ↓reduceIte] at hTy
              have hp : p.ty = .i1 := isI1Ty_eq_true p.ty h1
              rw [hp] at hw
              have hAg1 : EnvTypedAgree (Γ.bind p.id .i1) (env.bind p.id v)
                  (bindReg st (varReg p.id) (.bits .i64 w)).regs :=
                envTypedAgree_bind_var Γ env st.regs p.id .i1 v w hAgree hw
              rcases ih (Γ.bind p.id .i1) (env.bind p.id v)
                (bindReg st (varReg p.id) (.bits .i64 w)) vs' ws hAg1 hTy hws with
                ⟨st', hBind, hMem, hGlob, hAg'⟩
              exact ⟨st', hBind, hMem, hGlob, hAg'⟩
            · simp [h1] at hTy

/-- End-to-end lowering soundness for `LLVMLower.lowerDecl`:
if `lowerDecl d = some fn`, the arguments `argVals` encode to `llvmArgs`, and
source evaluation `evalCode` produces `retVal` on `HeapState.empty`, then executing
`fn` via `LLVMAst.execFn` with `codeBlockFuel d.body ≤ fuel` returns the exact
64-bit word encoding of `retVal` (never UB, poison, or wrong bits). -/
theorem lowerToLLVM_sound
    (d : LNIRDecl) (fn : LLVMFn) (argVals : List Val)
    (llvmArgs : List LLVMVal) (retVal : Val) (fuel : Nat)
    (hLower : lowerDecl d = some fn)
    (hArgs : encodeParamArgs d.params argVals = some llvmArgs)
    (hEval : evalCode 2 (bindParamEnv VarEnv.empty d.params argVals) HeapState.empty d.body =
      .ok (retVal, HeapState.empty))
    (hFuel : codeBlockFuel d.body ≤ fuel) :
    ∃ w, encodeScalarVal retVal = some w ∧
      execFn (modOfFn fn) fn llvmArgs fuel = .returned (some (.bits .i64 w)) := by
  dsimp [lowerDecl] at hLower
  cases hΓ0 : initParamTyEnv d.params with
  | none => simp [hΓ0] at hLower
  | some Γ0 =>
    simp only [hΓ0, Option.bind] at hLower
    cases hLow : lowerCode Γ0 entryLabel none d.body 0 0 with
    | none => simp [hLow] at hLower
    | some rc =>
      simp only [hLow] at hLower
      by_cases hs : sameScalarTy rc.ty d.retTy = true
      · simp only [hs, ↓reduceIte, Option.some.injEq] at hLower
        have hInit : initParamTyEnvAcc ScalarTyEnv.empty d.params = some Γ0 := hΓ0
        rcases bindParams_post ScalarTyEnv.empty VarEnv.empty
          { mem := {}, globals := [] } d.params argVals Γ0 llvmArgs
          empty_envTypedAgree hInit hArgs with ⟨st0, hBind, _, _, hAg0⟩
        have hFnBlks : fn.blocks = rc.entryBlk :: rc.restBlks := by
          rw [← hLower]
        have hFnParams : fn.params = (d.params.map fun p => ⟨varReg p.id, w64, []⟩) := by
          rw [← hLower]
        rcases lowerCode_sound Γ0 (bindParamEnv VarEnv.empty d.params argVals)
          d.body st0 0 0 rc (modOfFn fn) fn fuel retVal
          hAg0 hLow hFnBlks hFuel hEval with ⟨w, hEnc, hExec⟩
        refine ⟨w, hEnc, ?_⟩
        unfold execFn
        have hGlob : initGlobals (modOfFn fn) = some ({}, []) := rfl
        rw [hGlob, hFnBlks, hFnParams]
        simp only [hBind]
        exact hExec
      · simp [hs] at hLower

/-! ## 2. Non-Vacuity Witness (Multi-Block `ite` Diamond) -/

/-- Concrete `ite` diamond declaration: `if a < b then b - a else a - b`. -/
def absDiffDecl : LNIRDecl :=
  { name := "abs_diff"
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := .i64
  , body :=
      .letBind 2 .i1 (.scalar (.binOp .lt (.var 0) (.var 1)))
        (.ite 2
          (.letBind 3 .i64 (.scalar (.binOp .sub (.var 1) (.var 0))) (.ret 3))
          (.letBind 4 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 4))) }

/-- Non-vacuity witness exercising `lowerToLLVM_sound` end-to-end on a 2-parameter
`ite` diamond with `PhiNode` join on concrete inputs `(3, 10) ↦ 7`. -/
theorem lowerToLLVM_nonvacuous (fuel : Nat) (hFuel : codeBlockFuel absDiffDecl.body ≤ fuel) :
    ∃ fn,
      lowerDecl absDiffDecl = some fn ∧
      evalCode 2 (bindParamEnv VarEnv.empty absDiffDecl.params [.u64 3, .u64 10])
        HeapState.empty absDiffDecl.body = .ok (.u64 7, HeapState.empty) ∧
      execFn (modOfFn fn) fn [.bits .i64 3#64, .bits .i64 10#64] fuel =
        .returned (some (.bits .i64 7#64)) := by
  cases hLow : lowerDecl absDiffDecl with
  | none => nomatch hLow
  | some fn =>
    have hArgs : encodeParamArgs absDiffDecl.params [.u64 3, .u64 10] =
        some [.bits .i64 3#64, .bits .i64 10#64] := rfl
    have hEv : evalCode 2 (bindParamEnv VarEnv.empty absDiffDecl.params [.u64 3, .u64 10])
        HeapState.empty absDiffDecl.body = .ok (.u64 7, HeapState.empty) := rfl
    rcases lowerToLLVM_sound absDiffDecl fn [.u64 3, .u64 10]
      [.bits .i64 3#64, .bits .i64 10#64] (.u64 7) fuel hLow hArgs hEv hFuel with
      ⟨w, hEnc, hExec⟩
    have hw : w = 7#64 := by
      simp [encodeScalarVal] at hEnc
      exact hEnc.symm
    subst hw
    exact ⟨fn, rfl, hEv, hExec⟩

/-! ## 3. Emitter Mutant Kills (`M1`..`M5`) -/

def st2 (x y : BitVec 64) : ExecState :=
  { regs := [("v1", .bits .i64 y), ("v0", .bits .i64 x)] }

theorem runReturned_any_fuel (name : String) (body : List LLVMInstr)
    (x y w : BitVec 64) (fuel : Nat) (st' : ExecState)
    (hFuel : 1 ≤ fuel)
    (hEx : execInstrsWith (runCallWith { fns := [fnOf name body] } fuel) (st2 x y) body = .inr st')
    (hRes : st'.regs.lookup "res" = some (.bits .i64 w)) :
    runFn2 (fnOf name body) x y fuel = .returned (some (.bits .i64 w)) := by
  cases fuel with
  | zero => omega
  | succ f =>
    change calleeResToOutcome
      (match execInstrsWith (runCallWith { fns := [fnOf name body] } (f + 1)) (st2 x y) body with
       | .inl (.returned rv) => .returned rv (st2 x y).mem
       | .inl (.ub msg) => .ub msg
       | .inl .outOfFuel => .outOfFuel
       | .inr st1 => .returned (some (evalTypedOperand st1 w64 (.reg "res"))) st1.mem) =
      .returned (some (.bits .i64 w))
    rw [hEx]
    simp [calleeResToOutcome, evalTypedOperand, evalOperand, lookupReg, hRes]

theorem runUb_any_fuel (name : String) (body : List LLVMInstr)
    (x y : BitVec 64) (fuel : Nat) (msg : String)
    (hFuel : 1 ≤ fuel)
    (hEx : execInstrsWith (runCallWith { fns := [fnOf name body] } fuel) (st2 x y) body = .inl (.ub msg)) :
    runFn2 (fnOf name body) x y fuel = .ub msg := by
  cases fuel with
  | zero => omega
  | succ f =>
    change calleeResToOutcome
      (match execInstrsWith (runCallWith { fns := [fnOf name body] } (f + 1)) (st2 x y) body with
       | .inl (.returned rv) => .returned rv (st2 x y).mem
       | .inl (.ub m) => .ub m
       | .inl .outOfFuel => .outOfFuel
       | .inr st1 => .returned (some (evalTypedOperand st1 w64 (.reg "res"))) st1.mem) =
      .ub msg
    rw [hEx]
    rfl

def subSpec : List LLVMInstr := [.sub "res" .none .i64 (.reg "v0") (.reg "v1")]

/-- `M1` kill: swapping `sub` operands (`b - a` vs `a - b`) changes `runFn2` on `(1, 2)`. -/
theorem mutant_m1_killed (fuel : Nat) (hFuel : 1 ≤ fuel) :
    runFn2 (fnOf "spec_sub" subSpec) (1#64) (2#64) fuel ≠
      runFn2 mutantM1 (1#64) (2#64) fuel := by
  have hS := runReturned_any_fuel "spec_sub" subSpec (1#64) (2#64) (1#64 - 2#64) fuel
    (bindReg (st2 (1#64) (2#64)) "res" (.bits .i64 (1#64 - 2#64))) hFuel rfl rfl
  have hM := runReturned_any_fuel "mutant_m1_sub_swap"
    [.sub "res" .none .i64 (.reg "v1") (.reg "v0")] (1#64) (2#64) (2#64 - 1#64) fuel
    (bindReg (st2 (1#64) (2#64)) "res" (.bits .i64 (2#64 - 1#64))) hFuel rfl rfl
  unfold mutantM1
  rw [hS, hM]
  intro h
  nomatch h

def shlSpec : List LLVMInstr :=
  [.and_ "amt" .i64 (.reg "v1") (c64 63), .shl "res" .none .i64 (.reg "v0") (.reg "amt")]

/-- `M2` kill: replacing `shl` with `lshr` changes `runFn2` on `(1, 1)` (`2` vs `0`). -/
theorem mutant_m2_killed (fuel : Nat) (hFuel : 1 ≤ fuel) :
    runFn2 (fnOf "spec_shl" shlSpec) (1#64) (1#64) fuel ≠
      runFn2 mutantM2 (1#64) (1#64) fuel := by
  have hS := runReturned_any_fuel "spec_shl" shlSpec (1#64) (1#64) (2#64) fuel
    (bindReg (bindReg (st2 (1#64) (1#64)) "amt" (.bits .i64 (1#64))) "res" (.bits .i64 (2#64)))
    hFuel rfl rfl
  have hM := runReturned_any_fuel "mutant_m2_shl_as_shr"
    [.and_ "amt" .i64 (.reg "v1") (c64 63), .lshr "res" false .i64 (.reg "v0") (.reg "amt")]
    (1#64) (1#64) (0#64) fuel
    (bindReg (bindReg (st2 (1#64) (1#64)) "amt" (.bits .i64 (1#64))) "res" (.bits .i64 (0#64)))
    hFuel rfl rfl
  unfold mutantM2
  rw [hS, hM]
  intro h
  nomatch h

def ultSpec : List LLVMInstr :=
  [.icmp "cmp" .ult w64 (.reg "v0") (.reg "v1"), .zext "res" .i1 (.reg "cmp") .i64]

/-- `M3` kill: relaxing `icmp ult i64` to `icmp ule i64` changes `runFn2` on `(3, 3)`. -/
theorem mutant_m3_killed (fuel : Nat) (hFuel : 1 ≤ fuel) :
    runFn2 (fnOf "spec_ult64" ultSpec) (3#64) (3#64) fuel ≠
      runFn2 mutantM3 (3#64) (3#64) fuel := by
  have hS := runReturned_any_fuel "spec_ult64" ultSpec (3#64) (3#64) (0#64) fuel
    (bindReg (bindReg (st2 (3#64) (3#64)) "cmp" (.bits .i1 (0#1))) "res" (.bits .i64 (0#64)))
    hFuel rfl rfl
  have hM := runReturned_any_fuel "mutant_m3_ult64_as_ule64"
    [.icmp "cmp" .ule w64 (.reg "v0") (.reg "v1"), .zext "res" .i1 (.reg "cmp") .i64]
    (3#64) (3#64) (1#64) fuel
    (bindReg (bindReg (st2 (3#64) (3#64)) "cmp" (.bits .i1 (1#1))) "res" (.bits .i64 (1#64)))
    hFuel rfl rfl
  unfold mutantM3
  rw [hS, hM]
  intro h
  nomatch h

/-- `M4` kill: relaxing `icmp ult i256` to `icmp ule i256` changes `runFn2` on `(5, 5)`. -/
theorem mutant_m4_killed (fuel : Nat) (hFuel : 1 ≤ fuel) :
    runFn2 specUlt256Fn (5#64) (5#64) fuel ≠
      runFn2 mutantM4 (5#64) (5#64) fuel := by
  have hS := runReturned_any_fuel "spec_ult256"
    [ .zext "w0" .i64 (.reg "v0") .i256
    , .zext "w1" .i64 (.reg "v1") .i256
    , .icmp "cmp" .ult w256 (.reg "w0") (.reg "w1")
    , .zext "res" .i1 (.reg "cmp") .i64 ]
    (5#64) (5#64) (0#64) fuel
    (bindReg (bindReg (bindReg (bindReg (st2 (5#64) (5#64))
      "w0" (.bits .i256 ((5#64).zeroExtend 256)))
      "w1" (.bits .i256 ((5#64).zeroExtend 256)))
      "cmp" (.bits .i1 (0#1))) "res" (.bits .i64 (0#64)))
    hFuel rfl rfl
  have hM := runReturned_any_fuel "mutant_m4_ult256_as_ule256"
    [ .zext "w0" .i64 (.reg "v0") .i256
    , .zext "w1" .i64 (.reg "v1") .i256
    , .icmp "cmp" .ule w256 (.reg "w0") (.reg "w1")
    , .zext "res" .i1 (.reg "cmp") .i64 ]
    (5#64) (5#64) (1#64) fuel
    (bindReg (bindReg (bindReg (bindReg (st2 (5#64) (5#64))
      "w0" (.bits .i256 ((5#64).zeroExtend 256)))
      "w1" (.bits .i256 ((5#64).zeroExtend 256)))
      "cmp" (.bits .i1 (1#1))) "res" (.bits .i64 (1#64)))
    hFuel rfl rfl
  unfold specUlt256Fn mutantM4
  rw [hS, hM]
  intro h
  nomatch h

/-- `M5` kill: unguarded `udiv` triggers `.ub "division by zero"` on `(7, 0)` whereas
the guarded sequence returns `0#64`. -/
theorem mutant_m5_killed (fuel : Nat) (hFuel : 1 ≤ fuel) :
    runFn2 specUdivGuardFn (7#64) (0#64) fuel ≠
      runFn2 mutantM5 (7#64) (0#64) fuel := by
  have hS := runReturned_any_fuel "spec_udiv_guard"
    ((emitDivRem 0 false (.reg "v0") (.reg "v1")).2.2 ++
      [.add "res" .none .i64 (.reg (tmpReg 3)) (c64 0)])
    (7#64) (0#64) (0#64) fuel
    (bindReg (bindReg (bindReg (bindReg (bindReg (st2 (7#64) (0#64))
      (tmpReg 0) (.bits .i1 (1#1)))
      (tmpReg 1) (.bits .i64 (1#64)))
      (tmpReg 2) (.bits .i64 (7#64)))
      (tmpReg 3) (.bits .i64 (0#64)))
      "res" (.bits .i64 (0#64)))
    hFuel rfl rfl
  have hM := runUb_any_fuel "mutant_m5_udiv_unguarded"
    [.udiv "res" false .i64 (.reg "v0") (.reg "v1")]
    (7#64) (0#64) fuel "division by zero" hFuel rfl
  unfold specUdivGuardFn mutantM5
  rw [hS, hM]
  intro h
  nomatch h

end LeanNative.Proofs
