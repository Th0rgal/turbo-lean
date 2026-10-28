import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Backend.Semantics

namespace LeanNative.Backend.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Machine-Checked Backend Lowering & ARM64 NEON $\mathbb{F}_{2^{128}}$ Proofs (`LeanNative.Proofs.BackendProofs`)

Milestone M5:
1. `lowerToLeanMLIR_sound`: Proves that whenever `LeanMLIR.lowerLNIRToMLIR code = .ok mlirCom` and
   `evalCode fuel env st code = .ok (v, st')`, evaluating `mlirCom` under the independent
   `LeanMLIR.denote` (`BitVec 64` + `PoisonOr`) semantics yields `.val (v, st')` (`0 sorryAx`).
2. `arm64_f128_kernel_refines_lnir`: Proves that executing the 8-instruction ARM64 NEON
   `PMULL`/`PMULL2`/`EOR`/polynomial-0x87 reduction butterfly schedule (`instructions_f128_ntt`)
   on `LNSym.ArmState` refines the LNIR $\mathbb{F}_{2^{128}}$ additive NTT butterfly specification
   (`evalLNIRF128NttSpec`) across arbitrary slice lengths (`0 sorryAx`).
-/

/-- Encode an LNIR `(VarEnv, HeapState)` pair into `LeanMLIR.EncodedMLIRState`. -/
def encodeState (env : VarEnv) (st : HeapState) : LeanMLIR.EncodedMLIRState :=
  { env := env, heap := st }

/-- Re-export `LeanMLIR.lowerLNIRToMLIR` in `LeanNative.Backend.Proofs`. -/
abbrev lowerLNIRToMLIR : LNIRCode → Except String LeanMLIR.LLVM.Com :=
  LeanMLIR.lowerLNIRToMLIR

/-- Soundness of `LeanMLIR.lowerScalarToMLIR` against `evalScalarExpr` and `LeanMLIR.denoteExpr`. -/
theorem lowerScalarToMLIR_sound (env : VarEnv) (se : ScalarExpr) (v : Val)
    (heval : evalScalarExpr env se = .ok v) :
    LeanMLIR.denoteExpr env (LeanMLIR.lowerScalarToMLIR se) = .val v := by
  induction se generalizing v with
  | constU64 n =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    simp [LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr]
  | constBool b =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    rfl
  | var id =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases h : env id with
    | none => simp [h] at heval
    | some val =>
      simp [h] at heval
      subst heval
      rfl
  | binOp op l r ihl ihr =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases hl : evalScalarExpr env l with
    | error _ => simp [hl] at heval
    | ok vl =>
      cases hr : evalScalarExpr env r with
      | error _ => simp [hl, hr] at heval
      | ok vr =>
        simp only [hl, hr] at heval
        rw [ihl vl hl, ihr vr hr]
        dsimp only
        rw [heval]
  | unaryOp op a iha =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases ha : evalScalarExpr env a with
    | error _ => simp [ha] at heval
    | ok va =>
      simp only [ha] at heval
      rw [iha va ha]
      dsimp only
      rw [heval]
  | select c t e ihc iht ihe =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases hc : evalScalarExpr env c with
    | error _ => simp [hc] at heval
    | ok vc =>
      simp only [hc] at heval
      rw [ihc vc hc]
      cases vc with
      | bool b =>
        cases b with
        | true => exact iht v heval
        | false => exact ihe v heval
      | u64 n =>
        dsimp only at heval ⊢
        split at heval <;> rename_i hcond <;> simp [hcond]
        · exact iht v heval
        · exact ihe v heval
      | u256 w =>
        dsimp only at heval ⊢
        split at heval <;> rename_i hcond <;> simp [hcond]
        · exact iht v heval
        · exact ihe v heval
      | _ => contradiction
  | fma a b c iha ihb ihc =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExpr] at heval ⊢
    cases ha : evalScalarExpr env a with
    | error _ => simp [ha] at heval
    | ok va =>
      cases hb : evalScalarExpr env b with
      | error _ => simp [ha, hb] at heval
      | ok vb =>
        simp only [ha, hb] at heval
        rw [iha va ha, ihb vb hb]
        dsimp only
        cases hmul : evalBinOp .mul va vb with
        | error _ => simp [hmul] at heval
        | ok vab =>
          cases hc : evalScalarExpr env c with
          | error _ => simp [hmul, hc] at heval
          | ok vc =>
            simp only [hmul, hc] at heval
            rw [ihc vc hc]
            dsimp only
            rw [heval]

/-- Milestone M5 (Item 1): Machine-checked soundness of `lowerLNIRToMLIR` (`lowerToLeanMLIR_sound`)
    against `LeanMLIR.denote` (`BitVec 64` + `PoisonOr` semantics, `0 sorryAx`). -/
theorem lowerToLeanMLIR_sound (code : LNIRCode) (mlirCom : LeanMLIR.LLVM.Com)
    (fuel : Nat) (env : VarEnv) (st : HeapState) (v : Val) (st' : HeapState)
    (h_lower : lowerLNIRToMLIR code = .ok mlirCom)
    (h_eval : evalCode fuel env st code = .ok (v, st')) :
    LeanMLIR.denote mlirCom (encodeState env st) = .val (v, st') := by
  unfold lowerLNIRToMLIR at h_lower
  induction code generalizing mlirCom env st v st' with
  | letBind dst ty val k ih =>
    cases val with
    | scalar se =>
      dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
      cases hk : LeanMLIR.lowerLNIRToMLIR k with
      | error _ => rw [hk] at h_lower; contradiction
      | ok k' =>
        rw [hk] at h_lower
        injection h_lower with heq
        subst heq
        dsimp [evalCode, evalExpr] at h_eval
        cases hse : evalScalarExpr env se with
        | error _ => rw [hse] at h_eval; contradiction
        | ok vse =>
          rw [hse] at h_eval
          dsimp [LeanMLIR.denote, encodeState]
          rw [lowerScalarToMLIR_sound env se vse hse]
          exact ih k' (env.bind dst vse) st v st' hk h_eval
    | _ =>
      simp [LeanMLIR.lowerLNIRToMLIR] at h_lower
  | ite condVar thenBranch elseBranch iht ihe =>
    dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
    cases ht : LeanMLIR.lowerLNIRToMLIR thenBranch with
    | error _ => rw [ht] at h_lower; contradiction
    | ok t' =>
      rw [ht] at h_lower
      cases he : LeanMLIR.lowerLNIRToMLIR elseBranch with
      | error _ => rw [he] at h_lower; contradiction
      | ok e' =>
        rw [he] at h_lower
        injection h_lower with heq
        subst heq
        dsimp [evalCode] at h_eval
        dsimp [LeanMLIR.denote, encodeState]
        cases hc : env condVar with
        | none => rw [hc] at h_eval; contradiction
        | some vc =>
          rw [hc] at h_eval
          cases vc with
          | bool b =>
            cases b with
            | true => exact iht t' env st v st' ht h_eval
            | false => exact ihe e' env st v st' he h_eval
          | u64 n =>
            dsimp only at h_eval ⊢
            split at h_eval <;> rename_i hcond <;> simp [hcond]
            · exact iht t' env st v st' ht h_eval
            · exact ihe e' env st v st' he h_eval
          | u256 w =>
            dsimp only at h_eval ⊢
            split at h_eval <;> rename_i hcond <;> simp [hcond]
            · exact iht t' env st v st' ht h_eval
            · exact ihe e' env st v st' he h_eval
          | _ => contradiction
  | ret retVar =>
    dsimp [LeanMLIR.lowerLNIRToMLIR] at h_lower
    injection h_lower with heq
    subst heq
    dsimp [evalCode] at h_eval
    dsimp [LeanMLIR.denote, encodeState]
    cases hv : env retVar with
    | none => rw [hv] at h_eval; contradiction
    | some val =>
      rw [hv] at h_eval
      injection h_eval with hpair
      rw [← hpair]
  | unreachable =>
    dsimp [evalCode] at h_eval
    contradiction
  | _ =>
    simp [LeanMLIR.lowerLNIRToMLIR] at h_lower

/-- Generate the ARM64 NEON instruction sequence for an $\mathbb{F}_{2^{128}}$ NTT butterfly over `indices`. -/
def instructions_f128_ntt (indices : List Nat) : List LNSym.Arm64Instr :=
  indices.foldr (fun idx acc => LNSym.butterflyStepInstrs idx ++ acc) []

/-- Evaluate the LNIR $\mathbb{F}_{2^{128}}$ additive NTT butterfly specification over `indices`,
    accumulating into `(accU, accV)`. -/
def evalLNIRF128NttLoop (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg)
    (accU accV : List LNSym.QReg) : List Nat → List LNSym.QReg × List LNSym.QReg
  | [] => (accU, accV)
  | idx :: rest =>
    let u := uSlice[idx]?.getD LNSym.QReg.zero
    let v := vSlice[idx]?.getD LNSym.QReg.zero
    let (u', v') := LNSym.gf128ButterflyLane u v tw
    evalLNIRF128NttLoop uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) rest

/-- Top-level LNIR $\mathbb{F}_{2^{128}}$ butterfly slice specification starting from empty output slices. -/
def evalLNIRF128NttSpec (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg)
    (indices : List Nat) : List LNSym.QReg × List LNSym.QReg :=
  evalLNIRF128NttLoop uSlice vSlice tw [] [] indices

/-- ABI invariant relating an `LNSym.ArmState` to input slices `(uSlice, vSlice)`, twiddle `tw` in `q0`,
    and accumulated outputs `(accU, accV)`. -/
def Arm64LoopStateInv (s : LNSym.ArmState) (uSlice vSlice : List LNSym.QReg)
    (tw : LNSym.QReg) (accU accV : List LNSym.QReg) : Prop :=
  s.validABI = true ∧
  s.sliceU = uSlice ∧
  s.sliceV = vSlice ∧
  s.readQ 0 = tw ∧
  s.outU = accU ∧
  s.outV = accV

/-- Entry ABI precondition for `arm64_f128_kernel_refines_lnir`. -/
def Arm64SliceABICorresponds (s0 : LNSym.ArmState) (uSlice vSlice : List LNSym.QReg)
    (tw : LNSym.QReg) : Prop :=
  Arm64LoopStateInv s0 uSlice vSlice tw [] []

/-- Symbolic execution lemma for one 8-instruction ARM64 NEON butterfly step (`butterflyStepInstrs idx`):
    proves that `PMULL`/`PMULL2`/`reducePoly0x87`/`VEOR` on registers `q0..q6` computes
    `LNSym.gf128ButterflyLane u v tw` and preserves `Arm64LoopStateInv`. -/
theorem runArm64_butterflyStepInstrs_inv (idx : Nat) (s : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (accU accV : List LNSym.QReg)
    (hinv : Arm64LoopStateInv s uSlice vSlice tw accU accV) :
    let u := uSlice[idx]?.getD LNSym.QReg.zero
    let v := vSlice[idx]?.getD LNSym.QReg.zero
    let (u', v') := LNSym.gf128ButterflyLane u v tw
    Arm64LoopStateInv (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s)
      uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) := by
  rcases hinv with ⟨hvalid, hsu, hsv, hq0, houtU, houtV⟩
  dsimp [LNSym.butterflyStepInstrs, LNSym.runArm64, LNSym.execInstr,
         LNSym.ArmState.readQ, LNSym.ArmState.writeQ,
         LNSym.gf128ButterflyLane, LNSym.QReg.mulGF128,
         Arm64LoopStateInv] at hq0 ⊢
  simp [hvalid, hsu, hsv, hq0, houtU, houtV]

/-- Inductive loop invariant across arbitrary index lists `indices : List Nat`. -/
theorem runArm64_instructions_f128_ntt_loop (indices : List Nat) (s : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (accU accV : List LNSym.QReg)
    (hinv : Arm64LoopStateInv s uSlice vSlice tw accU accV) :
    LNSym.extractSlice (LNSym.runArm64 (instructions_f128_ntt indices) s) =
      evalLNIRF128NttLoop uSlice vSlice tw accU accV indices := by
  induction indices generalizing s accU accV with
  | nil =>
    rcases hinv with ⟨_, _, _, _, houtU, houtV⟩
    simp [instructions_f128_ntt, LNSym.runArm64, LNSym.extractSlice, evalLNIRF128NttLoop, houtU, houtV]
  | cons idx rest ih =>
    dsimp [instructions_f128_ntt, evalLNIRF128NttLoop]
    rw [LNSym.runArm64_append]
    have hstep := runArm64_butterflyStepInstrs_inv idx s uSlice vSlice tw accU accV hinv
    exact ih (LNSym.runArm64 (LNSym.butterflyStepInstrs idx) s)
      (accU ++ [(LNSym.gf128ButterflyLane (uSlice[idx]?.getD LNSym.QReg.zero) (vSlice[idx]?.getD LNSym.QReg.zero) tw).1])
      (accV ++ [(LNSym.gf128ButterflyLane (uSlice[idx]?.getD LNSym.QReg.zero) (vSlice[idx]?.getD LNSym.QReg.zero) tw).2])
      hstep

/-- Milestone M5 (Item 2): Machine-checked refinement of the 8-instruction ARM64 NEON
    $\mathbb{F}_{2^{128}}$ `PMULL`/`PMULL2`/polynomial-`0x87` butterfly kernel against `evalLNIRF128NttSpec`
    (`arm64_f128_kernel_refines_lnir`, `0 sorryAx`). -/
theorem arm64_f128_kernel_refines_lnir (s0 : LNSym.ArmState)
    (uSlice vSlice : List LNSym.QReg) (tw : LNSym.QReg) (indices : List Nat)
    (h_abi : Arm64SliceABICorresponds s0 uSlice vSlice tw) :
    LNSym.extractSlice (LNSym.runArm64 (instructions_f128_ntt indices) s0) =
      evalLNIRF128NttSpec uSlice vSlice tw indices :=
  runArm64_instructions_f128_ntt_loop indices s0 uSlice vSlice tw [] [] h_abi

end LeanNative.Backend.Proofs
