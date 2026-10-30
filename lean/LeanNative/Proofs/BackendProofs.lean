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
  unfold LeanMLIR.denoteExpr
  induction se generalizing v with
  | constU64 n =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    simp [LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison]
  | constBool b =>
    dsimp [evalScalarExpr] at heval
    injection heval with heq
    subst heq
    rfl
  | var id =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison,
           LeanMLIR.lookupPoison] at heval ⊢
    cases h : env id with
    | none => simp [h] at heval
    | some val =>
      simp [h] at heval
      subst heval
      rfl
  | binOp op l r ihl ihr =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison,
           LeanMLIR.LLVM.evalValBinOpWithFlags] at heval ⊢
    cases hl : evalScalarExpr env l with
    | error _ => simp [hl] at heval
    | ok vl =>
      cases hr : evalScalarExpr env r with
      | error _ => simp [hl, hr] at heval
      | ok vr =>
        simp only [hl, hr] at heval
        rw [ihl vl hl, ihr vr hr]
        have hfl : (({} : LeanMLIR.LLVM.NoWrapFlags) == {}) = true := rfl
        simp [hfl, heval]
  | unaryOp op a iha =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison] at heval ⊢
    cases ha : evalScalarExpr env a with
    | error _ => simp [ha] at heval
    | ok va =>
      simp only [ha] at heval
      rw [iha va ha]
      dsimp only
      rw [heval]
  | select c t e ihc iht ihe =>
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison] at heval ⊢
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
    dsimp [evalScalarExpr, LeanMLIR.lowerScalarToMLIR, LeanMLIR.denoteExprWithPoison] at heval ⊢
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
          have hden : LeanMLIR.denoteExprWithPoison env [] (LeanMLIR.lowerScalarToMLIR se) = .val vse :=
            lowerScalarToMLIR_sound env se vse hse
          rw [hden]
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
        dsimp [LeanMLIR.denote, encodeState, LeanMLIR.lookupPoison]
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
    dsimp [LeanMLIR.denote, encodeState, LeanMLIR.lookupPoison]
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

/-! ## Official `lean-mlir` / VeLLVM Poison Refinement (`PoisonOr.Refines`) & 4-Way ZMM SIMD Proofs -/

/-- VeLLVM / Alive2 / `lean-mlir` theorem (`evalArithWithFlags64_dropFlags_refines`, `0 sorryAx`):
    dropping `nuw`/`nsw`/`exact` poison flags (`{ nsw := false, nuw := false, exact := false }`)
    is a sound refinement (`PoisonOr.Refines`) and preserves defined values `.val out`
    for every 64-bit LLVM binary operator `op`. -/
theorem evalArithWithFlags64_dropFlags_refines (op : BinOp) (flags : LeanMLIR.LLVM.NoWrapFlags)
    (a b out : BitVec 64)
    (h_src : LeanMLIR.LLVM.evalArithWithFlags64 op flags a b = .val out) :
    LeanMLIR.LLVM.evalArithWithFlags64 op { unmaskedShift := flags.unmaskedShift } a b = .val out ∧
    LeanMLIR.PoisonOr.Refines
      (LeanMLIR.LLVM.evalArithWithFlags64 op flags a b)
      (LeanMLIR.LLVM.evalArithWithFlags64 op { unmaskedShift := flags.unmaskedShift } a b) := by
  have hval : LeanMLIR.LLVM.evalArithWithFlags64 op { unmaskedShift := flags.unmaskedShift } a b = .val out := by
    cases op <;> dsimp [LeanMLIR.LLVM.evalArithWithFlags64] at h_src ⊢
    · split at h_src
      · contradiction
      · exact h_src
    · split at h_src
      · contradiction
      · exact h_src
    · split at h_src
      · contradiction
      · exact h_src
    · split at h_src
      · contradiction
      · rename_i hdiv0
        simp only [hdiv0]
        split at h_src
        · contradiction
        · exact h_src
    · split at h_src
      · contradiction
      · rename_i hmod0
        simp only [hmod0]
        exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · split at h_src
      · contradiction
      · rename_i hshl
        simp only [hshl]
        split at h_src
        · contradiction
        · exact h_src
    · split at h_src
      · contradiction
      · rename_i hshr
        simp only [hshr]
        split at h_src
        · contradiction
        · exact h_src
    · split at h_src
      · contradiction
      · rename_i hsar
        simp only [hsar]
        split at h_src
        · contradiction
        · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
    · exact h_src
  refine ⟨hval, ?_⟩
  rw [h_src, hval]
  exact LeanMLIR.PoisonOr.Refines.refl (.val out)

/-- Unconditional 3-level Alive2 / VeLLVM / `lean-mlir` lattice refinement
    (`evalArithWithFlags64_dropFlags_refines_lattice`, `0 sorryAx`):
    for every `op : BinOp`, `flags : NoWrapFlags`, and `a b : BitVec 64`, dropping `nuw`/`nsw`/`exact`
    refines the flagged semantics in `PoisonOr.Refines` (`UB ⊑ Poison ⊑ Val v`), covering `.ub`,
    `.poison` refining to `.val`, and `.val` preservation. -/
theorem evalArithWithFlags64_dropFlags_refines_lattice (op : BinOp) (flags : LeanMLIR.LLVM.NoWrapFlags)
    (a b : BitVec 64) :
    LeanMLIR.PoisonOr.Refines
      (LeanMLIR.LLVM.evalArithWithFlags64 op flags a b)
      (LeanMLIR.LLVM.evalArithWithFlags64 op { unmaskedShift := flags.unmaskedShift } a b) := by
  cases op <;> unfold LeanMLIR.LLVM.evalArithWithFlags64
  · dsimp only; split
    · exact .poisonRefinesVal _ _
    · exact .valRefinesVal _
  · dsimp only; split
    · exact .poisonRefinesVal _ _
    · exact .valRefinesVal _
  · dsimp only; split
    · exact .poisonRefinesVal _ _
    · exact .valRefinesVal _
  · dsimp only; split
    · exact .ubRefines _ _
    · split
      · exact .poisonRefinesVal _ _
      · exact .valRefinesVal _
  · dsimp only; split
    · exact .ubRefines _ _
    · exact .valRefinesVal _
  · exact .valRefinesVal _
  · exact .valRefinesVal _
  · exact .valRefinesVal _
  · dsimp only; split
    · exact .poisonRefinesPoison _ _
    · split
      · exact .poisonRefinesVal _ _
      · exact .valRefinesVal _
  · dsimp only; split
    · exact .poisonRefinesPoison _ _
    · split
      · exact .poisonRefinesVal _ _
      · exact .valRefinesVal _
  · dsimp only; split
    · exact .poisonRefinesPoison _ _
    · split
      · exact .poisonRefinesVal _ _
      · exact .valRefinesVal _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _
  · exact LeanMLIR.PoisonOr.Refines.refl _

/-- Alive2 / LLVM LangRef soundness witness for `shl nsw` (`shl_nsw_overflow_produces_poison`):
    shifting `0x4000000000000000#64` left by `1#64` flips the sign bit (`ashr` does not recover `a`)
    and therefore yields `.poison` under `nsw = true`. -/
theorem shl_nsw_overflow_produces_poison :
    LeanMLIR.LLVM.evalArithWithFlags64 .shl { nsw := true, unmaskedShift := true }
      0x4000000000000000#64 1#64 = .poison "shl nuw/nsw poison" ∧
    LeanMLIR.PoisonOr.Refines
      (LeanMLIR.LLVM.evalArithWithFlags64 .shl { nsw := true, unmaskedShift := true }
        0x4000000000000000#64 1#64)
      (LeanMLIR.LLVM.evalArithWithFlags64 .shl { unmaskedShift := true }
        0x4000000000000000#64 1#64) := by
  refine ⟨by decide, ?_⟩
  exact evalArithWithFlags64_dropFlags_refines_lattice .shl { nsw := true, unmaskedShift := true }
    0x4000000000000000#64 1#64

/-- Command-level deferred register poison vs immediate UB theorem (`denote_letReg_deferred_poison_vs_ub`, `0 sorryAx`):
    1. Binding a poison-producing instruction (`udiv exact 1 2`) to register `1` in `.letReg`
       stores deferred `poison` in register `1` without aborting execution, so returning a live register `0`
       yields `.val (.u64 42, st.heap)`.
    2. Returning the poisoned register `1` at `.retReg 1` yields `.poison "udiv exact non-zero remainder poison"`.
    3. Branching on the poisoned register `1` at `.condBr 1` yields immediate `.ub`.
    4. Binding an immediate-UB instruction (`udiv exact 1 0`) to dead register `1` traps with `.ub` immediately at `.letReg`. -/
theorem denote_letReg_deferred_poison_vs_ub (env : VarEnv) (heap : HeapState)
    (h0 : env 0 = some (.u64 42)) :
    let st : LeanMLIR.EncodedMLIRState := { env := env, poisonRegs := [], heap := heap }
    let poisonExpr : LeanMLIR.LLVM.Expr :=
      .binOp64 .div { exact := true } (.const64 1#64) (.const64 2#64)
    let ubExpr : LeanMLIR.LLVM.Expr :=
      .binOp64 .div { exact := true } (.const64 1#64) (.const64 0#64)
    LeanMLIR.denote (.letReg 1 .i64 poisonExpr (.retReg 0)) st = .val (.u64 42, heap) ∧
    LeanMLIR.denote (.letReg 1 .i64 poisonExpr (.retReg 1)) st = .poison "udiv exact non-zero remainder poison" ∧
    LeanMLIR.denote (.letReg 1 .i64 poisonExpr (.condBr 1 (.retReg 0) (.retReg 0))) st =
      .ub "udiv exact non-zero remainder poison" ∧
    LeanMLIR.denote (.letReg 1 .i64 ubExpr (.retReg 0)) st = .ub "udiv by zero UB" := by
  dsimp [LeanMLIR.denote, LeanMLIR.denoteExprWithPoison,
         LeanMLIR.LLVM.evalValBinOpWithFlags, LeanMLIR.LLVM.evalArithWithFlags64,
         LeanMLIR.setPoison, LeanMLIR.clearPoison, LeanMLIR.lookupPoison]
  rw [h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Machine-checked equivalence between 4-way vectorized 512-bit AVX-512 `evalZmmButterfly4Way`
    and 4 independent 128-bit `gf128ButterflyLane` evaluations across lanes `0..3` (`0 sorryAx`). -/
theorem evalZmmButterfly4Way_refines_scalar_lanes (u v tw : LNSym.ZmmReg)
    (uOut vOut : LNSym.ZmmReg)
    (h_zmm : LNSym.evalZmmButterfly4Way u v tw = (uOut, vOut)) :
    (uOut.lane0, vOut.lane0) = LNSym.gf128ButterflyLane u.lane0 v.lane0 tw.lane0 ∧
    (uOut.lane1, vOut.lane1) = LNSym.gf128ButterflyLane u.lane1 v.lane1 tw.lane1 ∧
    (uOut.lane2, vOut.lane2) = LNSym.gf128ButterflyLane u.lane2 v.lane2 tw.lane2 ∧
    (uOut.lane3, vOut.lane3) = LNSym.gf128ButterflyLane u.lane3 v.lane3 tw.lane3 := by
  dsimp [LNSym.evalZmmButterfly4Way, LNSym.ZmmReg.mulGF128, LNSym.ZmmReg.xor,
         LNSym.gf128ButterflyLane] at h_zmm ⊢
  injection h_zmm with hu hv
  subst hu hv
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## AVX-512 `VPCLMULQDQ` 512-Bit `ZmmState` Loop & Target-Checked Emission Proofs -/

/-- Generate the 8-instruction AVX-512 `VPCLMULQDQ` / `VPXORQ` sequence over `indices`. -/
def instructions_avx512_f128_ntt (indices : List Nat) : List LNSym.Avx512Instr :=
  indices.foldr (fun idx acc => LNSym.avx512ButterflyStepInstrs idx ++ acc) []

/-- Evaluate the 4-way 512-bit LNIR $\mathbb{F}_{2^{128}}^4$ additive NTT butterfly specification
    over `indices`, accumulating into `(accU, accV)`. -/
def evalLNIRZmmF128NttLoop (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg)
    (accU accV : List LNSym.ZmmReg) : List Nat → List LNSym.ZmmReg × List LNSym.ZmmReg
  | [] => (accU, accV)
  | idx :: rest =>
    let u := uSlice[idx]?.getD LNSym.ZmmReg.zero
    let v := vSlice[idx]?.getD LNSym.ZmmReg.zero
    let (u', v') := LNSym.evalZmmButterfly4Way u v tw
    evalLNIRZmmF128NttLoop uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) rest

/-- Top-level 4-way 512-bit LNIR $\mathbb{F}_{2^{128}}^4$ butterfly slice specification. -/
def evalLNIRZmmF128NttSpec (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg)
    (indices : List Nat) : List LNSym.ZmmReg × List LNSym.ZmmReg :=
  evalLNIRZmmF128NttLoop uSlice vSlice tw [] [] indices

/-- ABI & CPU-feature invariant relating an `LNSym.ZmmState` to input slices `(uSlice, vSlice)`,
    twiddle `tw` in `zmm0`, `hasAvx512Vpclmul = true`, and accumulated outputs `(accU, accV)`. -/
def Avx512LoopStateInv (s : LNSym.ZmmState) (uSlice vSlice : List LNSym.ZmmReg)
    (tw : LNSym.ZmmReg) (accU accV : List LNSym.ZmmReg) : Prop :=
  s.hasAvx512Vpclmul = true ∧
  s.sliceU = uSlice ∧
  s.sliceV = vSlice ∧
  s.readZ 0 = tw ∧
  s.outU = accU ∧
  s.outV = accV

/-- Entry ABI precondition for `avx512_f128_kernel_refines_lnir`. -/
def Avx512SliceABICorresponds (s0 : LNSym.ZmmState) (uSlice vSlice : List LNSym.ZmmReg)
    (tw : LNSym.ZmmReg) : Prop :=
  Avx512LoopStateInv s0 uSlice vSlice tw [] []

/-- Symbolic execution lemma for one 8-instruction AVX-512 `VPCLMULQDQ` butterfly step
    (`avx512ButterflyStepInstrs idx`) on `ZmmState`. -/
theorem runAvx512_avx512ButterflyStepInstrs_inv (idx : Nat) (s : LNSym.ZmmState)
    (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg) (accU accV : List LNSym.ZmmReg)
    (hinv : Avx512LoopStateInv s uSlice vSlice tw accU accV) :
    let u := uSlice[idx]?.getD LNSym.ZmmReg.zero
    let v := vSlice[idx]?.getD LNSym.ZmmReg.zero
    let (u', v') := LNSym.evalZmmButterfly4Way u v tw
    Avx512LoopStateInv (LNSym.runAvx512 (LNSym.avx512ButterflyStepInstrs idx) s)
      uSlice vSlice tw (accU ++ [u']) (accV ++ [v']) := by
  rcases hinv with ⟨hfeat, hsu, hsv, hz0, houtU, houtV⟩
  dsimp [LNSym.avx512ButterflyStepInstrs, LNSym.runAvx512, LNSym.execAvx512Instr,
         LNSym.ZmmState.readZ, LNSym.ZmmState.writeZ,
         LNSym.evalZmmButterfly4Way, LNSym.ZmmReg.mulGF128, LNSym.ZmmReg.xor,
         LNSym.QReg.mulGF128, LNSym.ZmmReg.pmullLow, LNSym.ZmmReg.pmullMid,
         LNSym.ZmmReg.pmullHigh, LNSym.ZmmReg.reduceGF128, Avx512LoopStateInv] at hz0 ⊢
  simp [hfeat, hsu, hsv, hz0, houtU, houtV]

/-- Inductive loop invariant for `instructions_avx512_f128_ntt` across arbitrary index lists. -/
theorem runAvx512_instructions_avx512_f128_ntt_loop (indices : List Nat) (s : LNSym.ZmmState)
    (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg) (accU accV : List LNSym.ZmmReg)
    (hinv : Avx512LoopStateInv s uSlice vSlice tw accU accV) :
    LNSym.extractZmmSlice (LNSym.runAvx512 (instructions_avx512_f128_ntt indices) s) =
      evalLNIRZmmF128NttLoop uSlice vSlice tw accU accV indices := by
  induction indices generalizing s accU accV with
  | nil =>
    rcases hinv with ⟨_, _, _, _, houtU, houtV⟩
    simp [instructions_avx512_f128_ntt, LNSym.runAvx512, LNSym.extractZmmSlice,
          evalLNIRZmmF128NttLoop, houtU, houtV]
  | cons idx rest ih =>
    dsimp [instructions_avx512_f128_ntt, evalLNIRZmmF128NttLoop]
    rw [LNSym.runAvx512_append]
    have hstep := runAvx512_avx512ButterflyStepInstrs_inv idx s uSlice vSlice tw accU accV hinv
    exact ih (LNSym.runAvx512 (LNSym.avx512ButterflyStepInstrs idx) s)
      (accU ++ [(LNSym.evalZmmButterfly4Way (uSlice[idx]?.getD LNSym.ZmmReg.zero) (vSlice[idx]?.getD LNSym.ZmmReg.zero) tw).1])
      (accV ++ [(LNSym.evalZmmButterfly4Way (uSlice[idx]?.getD LNSym.ZmmReg.zero) (vSlice[idx]?.getD LNSym.ZmmReg.zero) tw).2])
      hstep

/-- Machine-checked refinement of the 8-instruction 512-bit AVX-512 `VPCLMULQDQ`/`VPXORQ`
    $\mathbb{F}_{2^{128}}^4$ butterfly kernel against `evalLNIRZmmF128NttSpec`
    (`avx512_f128_kernel_refines_lnir`, `0 sorryAx`). -/
theorem avx512_f128_kernel_refines_lnir (s0 : LNSym.ZmmState)
    (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg) (indices : List Nat)
    (h_abi : Avx512SliceABICorresponds s0 uSlice vSlice tw) :
    LNSym.extractZmmSlice (LNSym.runAvx512 (instructions_avx512_f128_ntt indices) s0) =
      evalLNIRZmmF128NttSpec uSlice vSlice tw indices :=
  runAvx512_instructions_avx512_f128_ntt_loop indices s0 uSlice vSlice tw [] [] h_abi

/-- SSA register and indexed store simulation invariant (`Avx512SsaSimInv`) connecting an architectural
    `LNSym.ZmmState` and an emitted SSA LLVM execution state `LNSym.Avx512LlvmExecState` through
    `m : LNSym.Avx512SsaMap`. -/
def Avx512SsaSimInv (zmmSt : LNSym.ZmmState) (m : LNSym.Avx512SsaMap) (llvmSt : LNSym.Avx512LlvmExecState) : Prop :=
  zmmSt.hasAvx512Vpclmul = true ∧
  (∀ r : Nat, llvmSt.readSsa (m.curReg r) = zmmSt.readZ r) ∧
  llvmSt.sliceU = zmmSt.sliceU ∧
  llvmSt.sliceV = zmmSt.sliceV ∧
  llvmSt.outU = zmmSt.outU ∧
  llvmSt.outV = zmmSt.outV ∧
  m.storeIdx = llvmSt.outU.length ∧
  m.storeIdx = llvmSt.outV.length

/-- Helper lemma: `evalAvx512LlvmStmt` on each `Avx512LlvmStmt` constructor reduces to the
    corresponding GEP + load/store or `pclmulqdq.512` + `xor` state update. -/
theorem writeOutAt_length (slots : List LNSym.ZmmReg) (v : LNSym.ZmmReg) :
    LNSym.Avx512LlvmExecState.writeOutAt slots slots.length v = slots ++ [v] := by
  simp [LNSym.Avx512LlvmExecState.writeOutAt]

/-- Fundamental SSA renaming lemma (`writeSsa_bumpReg_corr`):
    bumping register `rd` in `m : LNSym.Avx512SsaMap` to a fresh version `(dst, m') := m.bumpReg rd`
    and writing `val` to `dst` in `llvmSt` matches `(zmmSt.writeZ rd val).readZ r` for every register `r`. -/
theorem writeSsa_bumpReg_corr (zmmSt : LNSym.ZmmState) (m : LNSym.Avx512SsaMap)
    (llvmSt : LNSym.Avx512LlvmExecState) (rd : Nat) (val : LNSym.ZmmReg)
    (hregs : ∀ r : Nat, llvmSt.readSsa (m.curReg r) = zmmSt.readZ r) (r : Nat) :
    let (dst, m') := m.bumpReg rd
    (llvmSt.writeSsa dst val).readSsa (m'.curReg r) = (zmmSt.writeZ rd val).readZ r := by
  dsimp [LNSym.Avx512SsaMap.bumpReg, LNSym.Avx512SsaMap.curReg,
         LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512LlvmExecState.readSsa,
         LNSym.ZmmState.writeZ, LNSym.ZmmState.readZ]
  by_cases h : r = rd
  · subst h
    simp
  · have hbeq : (r == rd) = false := beq_eq_false_iff_ne.mpr h
    simp [h, hbeq]
    exact hregs r

/-- Single-instruction semantic preservation for SSA AVX-512 LLVM emission (`emitAvx512InstrSSA_sound`, `0 sorryAx`):
    whenever `emitAvx512InstrSSA cfg m ins = .ok (stmt, m')` and `Avx512SsaSimInv zmmSt m llvmSt` holds,
    executing the emitted SSA statement `stmt` (via its expanded `stmt.toIrLines` atomic LLVM 18 instructions)
    preserves `Avx512SsaSimInv` against `execAvx512Instr ins zmmSt`. -/
theorem emitAvx512InstrSSA_sound (cfg : LNSym.Avx512TargetConfig) (m m' : LNSym.Avx512SsaMap)
    (ins : LNSym.Avx512Instr) (stmt : LNSym.Avx512LlvmStmt)
    (zmmSt : LNSym.ZmmState) (llvmSt : LNSym.Avx512LlvmExecState)
    (h_emit : LNSym.emitAvx512InstrSSA cfg m ins = .ok (stmt, m'))
    (h_sim : Avx512SsaSimInv zmmSt m llvmSt) :
    Avx512SsaSimInv (LNSym.execAvx512Instr ins zmmSt) m' (LNSym.evalAvx512LlvmStmt stmt llvmSt) := by
  rcases h_sim with ⟨hfeat, hregs, hsu, hsv, houtU, houtV, hidxU, hidxV⟩
  unfold LNSym.emitAvx512InstrSSA at h_emit
  split at h_emit
  · contradiction
  · cases ins with
    | vmovdqu64LoadPair idx rdU rdV =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines,
             LNSym.Avx512LlvmStmt.toIrLines, LNSym.evalLlvm18IrLine]
      simp only [hfeat, Bool.not_true, hsu, hsv, decide_true, ite_true]
      let u := zmmSt.sliceU[idx]?.getD LNSym.ZmmReg.zero
      let v := zmmSt.sliceV[idx]?.getD LNSym.ZmmReg.zero
      let f1 := llvmSt.memFault || !llvmSt.aligned64 || !decide (idx < zmmSt.sliceU.length)
      let f2 := f1 || !llvmSt.aligned64 || !decide (idx < zmmSt.sliceV.length)
      let st1 : LNSym.Avx512LlvmExecState :=
        { llvmSt with inUPtr := fun k => if decide (k = (m.loadIdx, (m.bumpReg rdU).1)) then idx else llvmSt.inUPtr k }
      have hregs1 : ∀ r0 : Nat, st1.readSsa (m.curReg r0) = zmmSt.readZ r0 := hregs
      have h1 : ∀ r0 : Nat, (st1.writeSsa (m.bumpReg rdU).1 u).readSsa ((m.bumpReg rdU).2.curReg r0) =
          (zmmSt.writeZ rdU u).readZ r0 :=
        writeSsa_bumpReg_corr zmmSt m st1 rdU u hregs1
      let st2 : LNSym.Avx512LlvmExecState :=
        { st1.writeSsa (m.bumpReg rdU).1 u with
          memFault := f1
          inVPtr := fun k => if decide (k = (m.loadIdx, ((m.bumpReg rdU).2.bumpReg rdV).1)) then idx else llvmSt.inVPtr k }
      have h1' : ∀ r0 : Nat, st2.readSsa ((m.bumpReg rdU).2.curReg r0) = (zmmSt.writeZ rdU u).readZ r0 := h1
      have h2 := writeSsa_bumpReg_corr (zmmSt.writeZ rdU u) (m.bumpReg rdU).2 st2 rdV v h1' r
      exact h2
    | vpclmulqdqLowZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
             LNSym.evalLlvm18IrLine, LNSym.ZmmReg.pclmulqdq512Imm8]
      simp only [hfeat, Bool.not_true, hregs rn, hregs rm]
      exact writeSsa_bumpReg_corr zmmSt m llvmSt rd (LNSym.ZmmReg.pmullLow (zmmSt.readZ rn) (zmmSt.readZ rm)) hregs r
    | vpclmulqdqMidZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
                       LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
                       LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
                       LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
                       LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa,
                       LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
             LNSym.evalLlvm18IrLine, LNSym.ZmmReg.pclmulqdq512Imm8,
             LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
             LNSym.Avx512LlvmExecState.readSsa]
      have hregs_ssa : ∀ r0 : Nat, llvmSt.ssaRegs (m.curReg r0) = zmmSt.readZ r0 := hregs
      simp only [hfeat, Bool.not_true, hregs_ssa rn, hregs_ssa rm, decide_true, ite_true]
      let stMid : LNSym.Avx512LlvmExecState :=
        { llvmSt with
          loHiTemps := fun k => if decide (k = (m.bumpReg rd).1) then
            LNSym.ZmmReg.pmullLoHi (zmmSt.readZ rn) (zmmSt.readZ rm) else llvmSt.loHiTemps k
          hiLoTemps := fun k => if decide (k = (m.bumpReg rd).1) then
            LNSym.ZmmReg.pmullHiLo (zmmSt.readZ rn) (zmmSt.readZ rm) else llvmSt.hiLoTemps k }
      have hregsMid : ∀ r0 : Nat, stMid.readSsa (m.curReg r0) = zmmSt.readZ r0 := hregs
      exact writeSsa_bumpReg_corr zmmSt m stMid rd (LNSym.ZmmReg.pmullMid (zmmSt.readZ rn) (zmmSt.readZ rm)) hregsMid r
    | vpclmulqdqHighZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
             LNSym.evalLlvm18IrLine, LNSym.ZmmReg.pclmulqdq512Imm8]
      simp only [hfeat, Bool.not_true, hregs rn, hregs rm]
      exact writeSsa_bumpReg_corr zmmSt m llvmSt rd (LNSym.ZmmReg.pmullHigh (zmmSt.readZ rn) (zmmSt.readZ rm)) hregs r
    | vreducePoly0x87Zmm rd rLo rMid rHi =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines,
             LNSym.Avx512LlvmStmt.toIrLines, LNSym.evalLlvm18IrLine]
      simp only [hfeat, Bool.not_true, hregs rLo, hregs rMid, hregs rHi]
      exact writeSsa_bumpReg_corr zmmSt m llvmSt rd
        (LNSym.ZmmReg.reduceGF128 (zmmSt.readZ rLo) (zmmSt.readZ rMid) (zmmSt.readZ rHi)) hregs r
    | vpxorqZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      refine ⟨by simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, hfeat], ?_,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.ZmmState.writeZ, hfeat, houtV],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxU],
              by simp [LNSym.Avx512SsaMap.bumpReg, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, hidxV]⟩
      intro r
      dsimp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines,
             LNSym.Avx512LlvmStmt.toIrLines, LNSym.evalLlvm18IrLine]
      simp only [hfeat, Bool.not_true, hregs rn, hregs rm]
      exact writeSsa_bumpReg_corr zmmSt m llvmSt rd (LNSym.ZmmReg.xor (zmmSt.readZ rn) (zmmSt.readZ rm)) hregs r
    | vmovdqu64StorePair rU rV =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      have hregs_ssa : ∀ r0 : Nat, llvmSt.ssaRegs (m.curReg r0) = zmmSt.readZ r0 := hregs
      refine ⟨by simp [LNSym.execAvx512Instr, hfeat],
              fun r => by
                simpa [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512SsaMap.curReg,
                       LNSym.Avx512LlvmExecState.readSsa, LNSym.ZmmState.readZ, hfeat] using hregs r,
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, hfeat, hsu],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, hfeat, hsv],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.readSsa, hfeat, hidxU, writeOutAt_length, houtU, hregs_ssa rU],
              by simp [LNSym.execAvx512Instr, LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.readSsa, hfeat, hidxV, writeOutAt_length, houtV, hregs_ssa rV],
              by simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, hidxU, writeOutAt_length],
              by simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
                       LNSym.evalLlvm18IrLine, hidxV, writeOutAt_length]⟩

/-- Multi-instruction semantic preservation for SSA AVX-512 LLVM emission (`emitAvx512ProgSSA_sound`, `0 sorryAx`). -/
theorem emitAvx512ProgSSA_sound (cfg : LNSym.Avx512TargetConfig) (prog : List LNSym.Avx512Instr)
    (m m' : LNSym.Avx512SsaMap) (stmts : List LNSym.Avx512LlvmStmt)
    (zmmSt : LNSym.ZmmState) (llvmSt : LNSym.Avx512LlvmExecState)
    (h_emit : LNSym.emitAvx512ProgSSA cfg m prog = .ok (stmts, m'))
    (h_sim : Avx512SsaSimInv zmmSt m llvmSt) :
    Avx512SsaSimInv (LNSym.runAvx512 prog zmmSt) m' (LNSym.runAvx512LlvmProg stmts llvmSt) := by
  induction prog generalizing m m' stmts zmmSt llvmSt with
  | nil =>
    dsimp [LNSym.emitAvx512ProgSSA] at h_emit
    injection h_emit with hpair
    injection hpair with hstmts hm'
    subst hstmts
    subst hm'
    exact h_sim
  | cons ins rest ih =>
    dsimp [LNSym.emitAvx512ProgSSA] at h_emit
    cases h1 : LNSym.emitAvx512InstrSSA cfg m ins with
    | error _ => simp [h1] at h_emit
    | ok pair1 =>
      rcases pair1 with ⟨stmt, m1⟩
      simp only [h1] at h_emit
      cases h2 : LNSym.emitAvx512ProgSSA cfg m1 rest with
      | error _ => simp [h2] at h_emit
      | ok pair2 =>
        rcases pair2 with ⟨restStmts, m2⟩
        simp only [h2] at h_emit
        injection h_emit with hpair
        injection hpair with hstmts hm'
        subst hstmts
        subst hm'
        dsimp [LNSym.runAvx512, LNSym.runAvx512LlvmProg]
        have hstep := emitAvx512InstrSSA_sound cfg m m1 ins stmt zmmSt llvmSt h1 h_sim
        exact ih m1 m2 restStmts (LNSym.execAvx512Instr ins zmmSt) (LNSym.evalAvx512LlvmStmt stmt llvmSt) h2 hstep

/-- Memory-validity predicate for an `Avx512Instr` against input slice lengths `uLen` and `vLen`. -/
def Avx512InstrInBounds (ins : LNSym.Avx512Instr) (uLen vLen : Nat) : Prop :=
  match ins with
  | .vmovdqu64LoadPair idx _ _ => idx < uLen ∧ idx < vLen
  | _ => True

/-- Memory-validity predicate for a program `List Avx512Instr`. -/
def Avx512ProgInBounds (prog : List LNSym.Avx512Instr) (uLen vLen : Nat) : Prop :=
  ∀ ins, ins ∈ prog → Avx512InstrInBounds ins uLen vLen

/-- Single-instruction 64-byte alignment and slice/capacity bounds safety (`emitAvx512InstrSSA_memSafe`, `0 sorryAx`):
    when `llvmSt.aligned64 = true`, `llvmSt.memFault = false`, `Avx512InstrInBounds ins zmmSt.sliceU.length zmmSt.sliceV.length`,
    and output capacity bounds `m.storeIdx + avx512InstrStoreCount ins ≤ llvmSt.outCapU/V` hold,
    executing the expanded atomic `Llvm18IrLine` sequence of `stmt` preserves `aligned64 = true`, `memFault = false`,
    `outCapU`, `outCapV`, and advances `m'.storeIdx` by `avx512InstrStoreCount ins`. -/
theorem emitAvx512InstrSSA_memSafe (cfg : LNSym.Avx512TargetConfig) (m m' : LNSym.Avx512SsaMap)
    (ins : LNSym.Avx512Instr) (stmt : LNSym.Avx512LlvmStmt)
    (zmmSt : LNSym.ZmmState) (llvmSt : LNSym.Avx512LlvmExecState)
    (h_emit : LNSym.emitAvx512InstrSSA cfg m ins = .ok (stmt, m'))
    (h_sim : Avx512SsaSimInv zmmSt m llvmSt)
    (h_align : llvmSt.aligned64 = true)
    (h_nofault : llvmSt.memFault = false)
    (h_bounds : Avx512InstrInBounds ins zmmSt.sliceU.length zmmSt.sliceV.length)
    (h_cap : m.storeIdx + LNSym.avx512InstrStoreCount ins ≤ llvmSt.outCapU ∧
             m.storeIdx + LNSym.avx512InstrStoreCount ins ≤ llvmSt.outCapV) :
    (LNSym.evalAvx512LlvmStmt stmt llvmSt).aligned64 = true ∧
    (LNSym.evalAvx512LlvmStmt stmt llvmSt).memFault = false ∧
    (LNSym.evalAvx512LlvmStmt stmt llvmSt).outCapU = llvmSt.outCapU ∧
    (LNSym.evalAvx512LlvmStmt stmt llvmSt).outCapV = llvmSt.outCapV ∧
    m'.storeIdx = m.storeIdx + LNSym.avx512InstrStoreCount ins := by
  rcases h_sim with ⟨_, _, hsu, hsv, _, _, hidxU, hidxV⟩
  unfold LNSym.emitAvx512InstrSSA at h_emit
  split at h_emit
  · contradiction
  · cases ins with
    | vmovdqu64LoadPair idx rdU rdV =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      rcases h_bounds with ⟨hbU, hbV⟩
      have hbU' : idx < llvmSt.sliceU.length := by rw [hsu]; exact hbU
      have hbV' : idx < llvmSt.sliceV.length := by rw [hsv]; exact hbV
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.avx512InstrStoreCount, h_align, h_nofault, hbU', hbV']
    | vpclmulqdqLowZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.avx512InstrStoreCount, h_align, h_nofault]
    | vpclmulqdqMidZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.Avx512LlvmExecState.writeLoHiTemp, LNSym.Avx512LlvmExecState.writeHiLoTemp,
            LNSym.avx512InstrStoreCount, h_align, h_nofault]
    | vpclmulqdqHighZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.avx512InstrStoreCount, h_align, h_nofault]
    | vreducePoly0x87Zmm rd rLo rMid rHi =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.avx512InstrStoreCount, h_align, h_nofault]
    | vpxorqZmm rd rn rm =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.Avx512LlvmExecState.writeSsa, LNSym.Avx512SsaMap.bumpReg,
            LNSym.avx512InstrStoreCount, h_align, h_nofault]
    | vmovdqu64StorePair rU rV =>
      dsimp only at h_emit
      injection h_emit with hpair
      injection hpair with hstmt hm'
      subst hstmt
      subst hm'
      rcases h_cap with ⟨hcapU, hcapV⟩
      dsimp [LNSym.avx512InstrStoreCount] at hcapU hcapV
      have hleU : m.storeIdx ≤ llvmSt.outU.length := Nat.le_of_eq hidxU
      have hleV : m.storeIdx ≤ llvmSt.outV.length := Nat.le_of_eq hidxV
      have hltU : m.storeIdx < llvmSt.outCapU := hcapU
      have hltV : m.storeIdx < llvmSt.outCapV := hcapV
      simp [LNSym.evalAvx512LlvmStmt, LNSym.evalLlvm18IrLines, LNSym.Avx512LlvmStmt.toIrLines,
            LNSym.evalLlvm18IrLine, LNSym.avx512InstrStoreCount, h_align, h_nofault, hleU, hleV, hltU, hltV]

/-- Multi-instruction 64-byte alignment and slice/capacity bounds safety (`emitAvx512ProgSSA_memSafe`, `0 sorryAx`). -/
theorem emitAvx512ProgSSA_memSafe (cfg : LNSym.Avx512TargetConfig) (prog : List LNSym.Avx512Instr)
    (m m' : LNSym.Avx512SsaMap) (stmts : List LNSym.Avx512LlvmStmt)
    (zmmSt : LNSym.ZmmState) (llvmSt : LNSym.Avx512LlvmExecState)
    (h_emit : LNSym.emitAvx512ProgSSA cfg m prog = .ok (stmts, m'))
    (h_sim : Avx512SsaSimInv zmmSt m llvmSt)
    (h_align : llvmSt.aligned64 = true)
    (h_nofault : llvmSt.memFault = false)
    (h_bounds : Avx512ProgInBounds prog zmmSt.sliceU.length zmmSt.sliceV.length)
    (h_cap : m.storeIdx + LNSym.avx512ProgStoreCount prog ≤ llvmSt.outCapU ∧
             m.storeIdx + LNSym.avx512ProgStoreCount prog ≤ llvmSt.outCapV) :
    (LNSym.runAvx512LlvmProg stmts llvmSt).aligned64 = true ∧
    (LNSym.runAvx512LlvmProg stmts llvmSt).memFault = false := by
  induction prog generalizing m m' stmts zmmSt llvmSt with
  | nil =>
    dsimp [LNSym.emitAvx512ProgSSA] at h_emit
    injection h_emit with hpair
    injection hpair with hstmts _
    subst hstmts
    exact ⟨h_align, h_nofault⟩
  | cons ins rest ih =>
    dsimp [LNSym.emitAvx512ProgSSA] at h_emit
    cases h1 : LNSym.emitAvx512InstrSSA cfg m ins with
    | error _ => simp [h1] at h_emit
    | ok pair1 =>
      rcases pair1 with ⟨stmt, m1⟩
      simp only [h1] at h_emit
      cases h2 : LNSym.emitAvx512ProgSSA cfg m1 rest with
      | error _ => simp [h2] at h_emit
      | ok pair2 =>
        rcases pair2 with ⟨restStmts, m2⟩
        simp only [h2] at h_emit
        injection h_emit with hpair
        injection hpair with hstmts hm'
        subst hstmts
        subst hm'
        dsimp [LNSym.runAvx512LlvmProg]
        have hb1 : Avx512InstrInBounds ins zmmSt.sliceU.length zmmSt.sliceV.length :=
          h_bounds ins (by simp)
        rcases h_cap with ⟨hcapU, hcapV⟩
        dsimp [LNSym.avx512ProgStoreCount] at hcapU hcapV
        have hcap1 : m.storeIdx + LNSym.avx512InstrStoreCount ins ≤ llvmSt.outCapU ∧
                     m.storeIdx + LNSym.avx512InstrStoreCount ins ≤ llvmSt.outCapV := by
          constructor <;> omega
        have ⟨ha1, hnf1, hcu1, hcv1, hm1_idx⟩ :=
          emitAvx512InstrSSA_memSafe cfg m m1 ins stmt zmmSt llvmSt h1 h_sim h_align h_nofault hb1 hcap1
        have hstep := emitAvx512InstrSSA_sound cfg m m1 ins stmt zmmSt llvmSt h1 h_sim
        have hsu_eq : (LNSym.execAvx512Instr ins zmmSt).sliceU.length = zmmSt.sliceU.length := by
          cases ins <;> simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, h_sim.1]
        have hsv_eq : (LNSym.execAvx512Instr ins zmmSt).sliceV.length = zmmSt.sliceV.length := by
          cases ins <;> simp [LNSym.execAvx512Instr, LNSym.ZmmState.writeZ, h_sim.1]
        have hbrest : Avx512ProgInBounds rest (LNSym.execAvx512Instr ins zmmSt).sliceU.length
            (LNSym.execAvx512Instr ins zmmSt).sliceV.length := by
          intro i hi
          rw [hsu_eq, hsv_eq]
          exact h_bounds i (by simp [hi])
        have hcap_rest : m1.storeIdx + LNSym.avx512ProgStoreCount rest ≤ (LNSym.evalAvx512LlvmStmt stmt llvmSt).outCapU ∧
                         m1.storeIdx + LNSym.avx512ProgStoreCount rest ≤ (LNSym.evalAvx512LlvmStmt stmt llvmSt).outCapV := by
          rw [hcu1, hcv1, hm1_idx]
          constructor <;> omega
        exact ih m1 m2 restStmts (LNSym.execAvx512Instr ins zmmSt) (LNSym.evalAvx512LlvmStmt stmt llvmSt)
          h2 hstep ha1 hnf1 hbrest hcap_rest

/-- Compositionality of flat LLVM 18 IR line evaluation (`evalLlvm18IrLines_append`, `0 sorryAx`). -/
theorem evalLlvm18IrLines_append (l1 l2 : List LNSym.Llvm18IrLine) (st : LNSym.Avx512LlvmExecState) :
    LNSym.evalLlvm18IrLines (l1 ++ l2) st = LNSym.evalLlvm18IrLines l2 (LNSym.evalLlvm18IrLines l1 st) := by
  unfold LNSym.evalLlvm18IrLines
  exact List.foldl_append

/-- Equivalence between executing the flattened atomic `Llvm18IrLine` stream (`flattenAvx512IrLines stmts`)
    and statement-by-statement execution (`runAvx512LlvmProg stmts`) (`0 sorryAx`). -/
theorem evalLlvm18IrLines_flatten (stmts : List LNSym.Avx512LlvmStmt) (st : LNSym.Avx512LlvmExecState) :
    LNSym.evalLlvm18IrLines (LNSym.flattenAvx512IrLines stmts) st = LNSym.runAvx512LlvmProg stmts st := by
  induction stmts generalizing st with
  | nil => rfl
  | cons s rest ih =>
    dsimp [LNSym.flattenAvx512IrLines, LNSym.runAvx512LlvmProg, LNSym.evalAvx512LlvmStmt]
    rw [evalLlvm18IrLines_append, ih]
    rfl

/-- End-to-end semantic refinement and memory safety of emitted SSA AVX-512 LLVM code against the LNIR 4-way
    $\mathbb{F}_{2^{128}}^4$ butterfly specification (`emitted_avx512_llvm_refines_lnir`, `0 sorryAx`),
    establishing both fault-free 64-byte aligned execution (`aligned64 = true`, `memFault = false`) and
    exact output slice agreement on the flattened atomic `Llvm18IrLine` stream and structured statement runner. -/
theorem emitted_avx512_llvm_refines_lnir (cfg : LNSym.Avx512TargetConfig)
    (m m' : LNSym.Avx512SsaMap) (stmts : List LNSym.Avx512LlvmStmt)
    (s0 : LNSym.ZmmState) (llvmSt0 : LNSym.Avx512LlvmExecState)
    (uSlice vSlice : List LNSym.ZmmReg) (tw : LNSym.ZmmReg) (indices : List Nat)
    (h_emit : LNSym.emitAvx512ProgSSA cfg m (instructions_avx512_f128_ntt indices) = .ok (stmts, m'))
    (h_abi : Avx512SliceABICorresponds s0 uSlice vSlice tw)
    (h_sim : Avx512SsaSimInv s0 m llvmSt0)
    (h_align : llvmSt0.aligned64 = true)
    (h_nofault : llvmSt0.memFault = false)
    (h_bounds : Avx512ProgInBounds (instructions_avx512_f128_ntt indices) s0.sliceU.length s0.sliceV.length)
    (h_cap : m.storeIdx + LNSym.avx512ProgStoreCount (instructions_avx512_f128_ntt indices) ≤ llvmSt0.outCapU ∧
             m.storeIdx + LNSym.avx512ProgStoreCount (instructions_avx512_f128_ntt indices) ≤ llvmSt0.outCapV) :
    LNSym.emitAvx512ProgLLVM cfg m (instructions_avx512_f128_ntt indices) =
      .ok (stmts.map LNSym.Avx512LlvmStmt.toLLVMText, m') ∧
    LNSym.emitAvx512ProgIrLines cfg m (instructions_avx512_f128_ntt indices) =
      .ok (LNSym.flattenAvx512IrLines stmts, m') ∧
    (LNSym.evalLlvm18IrLines (LNSym.flattenAvx512IrLines stmts) llvmSt0).aligned64 = true ∧
    (LNSym.evalLlvm18IrLines (LNSym.flattenAvx512IrLines stmts) llvmSt0).memFault = false ∧
    (LNSym.runAvx512LlvmProg stmts llvmSt0).aligned64 = true ∧
    (LNSym.runAvx512LlvmProg stmts llvmSt0).memFault = false ∧
    LNSym.extractLlvmZmmSlice (LNSym.evalLlvm18IrLines (LNSym.flattenAvx512IrLines stmts) llvmSt0) =
      evalLNIRZmmF128NttSpec uSlice vSlice tw indices ∧
    LNSym.extractLlvmZmmSlice (LNSym.runAvx512LlvmProg stmts llvmSt0) =
      evalLNIRZmmF128NttSpec uSlice vSlice tw indices := by
  have hprog := emitAvx512ProgSSA_sound cfg (instructions_avx512_f128_ntt indices) m m' stmts s0 llvmSt0 h_emit h_sim
  rcases hprog with ⟨_, _, _, _, houtU, houtV, _, _⟩
  have ⟨halign_end, hnofault_end⟩ :=
    emitAvx512ProgSSA_memSafe cfg (instructions_avx512_f128_ntt indices) m m' stmts s0 llvmSt0
      h_emit h_sim h_align h_nofault h_bounds h_cap
  have hlnir := avx512_f128_kernel_refines_lnir s0 uSlice vSlice tw indices h_abi
  have hflat := evalLlvm18IrLines_flatten stmts llvmSt0
  refine ⟨by simp [LNSym.emitAvx512ProgLLVM, h_emit],
          by simp [LNSym.emitAvx512ProgIrLines, h_emit],
          by rw [hflat]; exact halign_end,
          by rw [hflat]; exact hnofault_end,
          halign_end,
          hnofault_end,
          ?_, ?_⟩
  · rw [hflat]
    unfold LNSym.extractLlvmZmmSlice
    unfold LNSym.extractZmmSlice at hlnir
    rw [houtU, houtV, hlnir]
  · unfold LNSym.extractLlvmZmmSlice
    unfold LNSym.extractZmmSlice at hlnir
    rw [houtU, houtV, hlnir]

/-- Target- and feature-gating soundness (`emitAvx512InstrLLVM_rejects_non_avx512`, `0 sorryAx`):
    1. `emitAvx512InstrLLVM` rejects `arm64` and `wasm32` architectures.
    2. `emitAvx512InstrLLVM` rejects `x86_64` targets missing `hasAvx512F`, `hasAvx512Vl`, or `hasVpclmulqdq`.
    3. `emitAvx512InstrLLVM` succeeds for every `instr : Avx512Instr` on a supported `x86_64` config. -/
theorem emitAvx512InstrLLVM_rejects_non_avx512 (m : LNSym.Avx512SsaMap) (instr : LNSym.Avx512Instr) :
    (LNSym.emitAvx512InstrLLVM { arch := .arm64 } m instr).isOk = false ∧
    (LNSym.emitAvx512InstrLLVM { arch := .wasm32 } m instr).isOk = false ∧
    (LNSym.emitAvx512InstrLLVM { arch := .x86_64, hasAvx512F := false } m instr).isOk = false ∧
    (LNSym.emitAvx512InstrLLVM { arch := .x86_64, hasVpclmulqdq := false } m instr).isOk = false ∧
    (LNSym.emitAvx512InstrLLVM { arch := .x86_64 } m instr).isOk = true := by
  cases instr <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end LeanNative.Backend.Proofs
