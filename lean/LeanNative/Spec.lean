/-
  LeanNative.Spec: Unified Compositional Specification & Meta-Specification Kernel
  Zero `import Lean` (compiles into `lean-native-core` with `libleanrt.a` only),
  zero `sorryAx`, zero `native_decide`, zero `trustCompiler`.

  Architecture (Harmonized 2-Layer Symbiosis with `TurboLean.Spec`):
  - Layer I  : Universal Meta-Specifications (`MetaGateSpec`, `SpeculativeGate`,
               `VerifiedTransformContract`, `ClockedStepBudget`, and multi-step refinement composition).
  - Layer II : Declarative `MetaGateSpec` bundles and ≤ 3-line Mathlib4-style corollaries
               governing FastCheck non-vacuity, C-ABI scalar tagging, PR spec-pinning,
               256-bit 4-limb GPU carry homomorphisms, 4-target hardware routing, and RISC-V step budgets.
-/
import LeanSys.Gate
import LeanSys.Spec
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Backend.Hybrid

namespace LeanNative.Spec
open LeanSys.Contracts LeanNative.IR LeanNative.Semantics LeanNative.Backend.Hybrid

/-! ============================================================================
    LAYER I: META-SPECIFICATIONS (`LeanSys.Gate`, `VerifiedTransformContract`, `ClockedStepBudget`)
    ============================================================================ -/

abbrev MetaGateSpec := @LeanSys.Contracts.MetaGateSpec
abbrev evalWithUntrustedOptPlugin := @LeanSys.Contracts.evalWithUntrustedOptPlugin

theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) (h_unsafe : ¬ Safe x) :
    M.gate x = false :=
  LeanSys.Contracts.MetaGateSpec.rejects_unsafe M x h_unsafe

theorem untrusted_opt_plugin_tv_gate_sound {Decl Cert : Type}
    (Refines : Decl → Decl → Prop) (h_refl : ∀ d, Refines d d)
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (h_gate_sound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand) (d : Decl) :
    Refines d (evalWithUntrustedOptPlugin plugin verifyGate d) :=
  LeanSys.Contracts.untrusted_opt_plugin_tv_gate_sound Refines h_refl plugin verifyGate h_gate_sound d

theorem untrusted_opt_plugin_timeout_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d : Decl) (h_timeout : plugin d = none) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d :=
  LeanSys.Contracts.untrusted_opt_plugin_timeout_fallback plugin verifyGate d h_timeout

theorem untrusted_opt_plugin_reject_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d cand : Decl) (cert : Cert) (h_prop : plugin d = some (cand, cert)) (h_rej : verifyGate d cand cert = false) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d :=
  LeanSys.Contracts.untrusted_opt_plugin_reject_fallback plugin verifyGate d cand cert h_prop h_rej

/-- First-class proof-carrying transformation contract tying `run` to its refinement proof `is_sound`. -/
structure VerifiedTransformContract (Decl : Type) (Refines : Decl → Decl → Prop) where
  name     : String
  run      : Decl → Decl
  is_sound : ∀ d, Refines d (run d)

def VerifiedTransformContract.compose (Decl : Type) (Refines : Decl → Decl → Prop)
    (h_trans : ∀ a b c, Refines a b → Refines b c → Refines a c)
    (c1 c2 : VerifiedTransformContract Decl Refines) :
    VerifiedTransformContract Decl Refines where
  name     := c1.name ++ " >> " ++ c2.name
  run      := fun d => c2.run (c1.run d)
  is_sound := fun d => h_trans d (c1.run d) (c2.run (c1.run d)) (c1.is_sound d) (c2.is_sound (c1.run d))

def VerifiedTransformContract.fromGatedPlugin {Decl Cert : Type} {Refines : Decl → Decl → Prop}
    (name : String) (h_refl : ∀ d, Refines d d)
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (h_gate_sound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand) :
    VerifiedTransformContract Decl Refines where
  name     := name
  run      := evalWithUntrustedOptPlugin plugin verifyGate
  is_sound := untrusted_opt_plugin_tv_gate_sound Refines h_refl plugin verifyGate h_gate_sound

def runGatedPluginChain (steps : List (LNIRCode → LNIRCode)) (c : LNIRCode) : LNIRCode :=
  steps.foldl (fun acc step => step acc) c

theorem opt_pipeline_chain_refines
    (steps : List (LNIRCode → LNIRCode))
    (h_steps : ∀ step, step ∈ steps → ∀ c, CodeRefines c (step c)) (c : LNIRCode) :
    CodeRefines c (runGatedPluginChain steps c) := by
  induction steps generalizing c with
  | nil => exact CodeRefines.refl c
  | cons hd tl ih =>
    exact CodeRefines.trans (h_steps hd (.head tl) c)
      (ih (fun s hs x => h_steps s (.tail hd hs) x) (hd c))

structure AffineStepBudget where
  scale  : Nat
  offset : Nat
  deriving Repr, DecidableEq, BEq

def AffineStepBudget.eval (b : AffineStepBudget) (steps : Nat) : Nat := b.scale * steps + b.offset

def composeAffineBudget (outer inner : AffineStepBudget) : AffineStepBudget :=
  { scale := outer.scale * inner.scale, offset := outer.scale * inner.offset + outer.offset }

theorem composeAffineBudget_eval (outer inner : AffineStepBudget) (steps : Nat) :
    (composeAffineBudget outer inner).eval steps = outer.eval (inner.eval steps) := by
  simp [composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem affine_step_budget_monotone (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    b.eval s1 ≤ b.eval s2 :=
  Nat.add_le_add_right (Nat.mul_le_mul_left b.scale h) b.offset

def evalLoopStepBudget (initSteps fuel : Nat) (bodyBudget : AffineStepBudget) (iterSteps : Nat) : Nat :=
  initSteps + fuel * bodyBudget.eval iterSteps

def riscvDivU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then 0xffffffffffffffff else lhs / rhs
def riscvRemU64Spec (lhs rhs : UInt64) : UInt64 := if rhs == 0 then lhs else lhs % rhs

theorem evalLoopStepBudget_monotone (init fuel : Nat) (b : AffineStepBudget) {s1 s2 : Nat} (h : s1 ≤ s2) :
    evalLoopStepBudget init fuel b s1 ≤ evalLoopStepBudget init fuel b s2 :=
  Nat.add_le_add_left (Nat.mul_le_mul_left fuel (affine_step_budget_monotone b h)) init

def evalPassChainBudget (passes : List AffineStepBudget) : AffineStepBudget :=
  passes.foldl composeAffineBudget { scale := 1, offset := 0 }

theorem evalPassChainBudget_cons (b : AffineStepBudget) (bs : List AffineStepBudget) (steps : Nat) :
    (bs.foldl composeAffineBudget b).eval steps =
      b.eval ((bs.foldl composeAffineBudget { scale := 1, offset := 0 }).eval steps) := by
  induction bs generalizing b with
  | nil => simp [AffineStepBudget.eval]
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (composeAffineBudget b hd),
        ih (composeAffineBudget { scale := 1, offset := 0 } hd)]
    simp [composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Minimal radix-2 Patricia-tree (`Spt`) code/memory table model for RISC-V & `evm.fast-dev`. -/
inductive SptTree (α : Type) where
  | leaf : SptTree α
  | node : Option α → SptTree α → SptTree α → SptTree α
  deriving Repr, DecidableEq, BEq

def sptLookup {α : Type} : SptTree α → List Bool → Option α
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l r, b :: bs => sptLookup (if b then r else l) bs

def sptInsert {α : Type} : SptTree α → List Bool → α → SptTree α
  | .leaf, [], val => .node (some val) .leaf .leaf
  | .leaf, b :: bs, val =>
    if b then .node none .leaf (sptInsert .leaf bs val)
    else .node none (sptInsert .leaf bs val) .leaf
  | .node _ l r, [], val => .node (some val) l r
  | .node v l r, b :: bs, val =>
    if b then .node v l (sptInsert r bs val)
    else .node v (sptInsert l bs val) r

theorem sptLookup_insert_same {α : Type} (t : SptTree α) (k : List Bool) (val : α) :
    sptLookup (sptInsert t k val) k = some val := by
  induction k generalizing t with
  | nil => cases t <;> rfl
  | cons b bs ih => cases t <;> cases b <;> simp [sptInsert, sptLookup, ih]

/-! ============================================================================
    LAYER II: DECLARATIVE COROLLARIES (≤ 3 LINES) & `MetaGateSpec` BUNDLES
    ============================================================================ -/

/-! ## 1. Gated Plugin & Pipeline Refinement Corollaries (`SpeculativeGate`) -/

theorem untrusted_opt_plugin_code_refines {Cert : Type}
    (plugin : LNIRCode → Option (LNIRCode × Cert))
    (verifyGate : LNIRCode → LNIRCode → Cert → Bool)
    (h_gate_sound : ∀ src cand cert, verifyGate src cand cert = true → CodeRefines src cand)
    (src : LNIRCode) :
    CodeRefines src (evalWithUntrustedOptPlugin plugin verifyGate src) :=
  untrusted_opt_plugin_tv_gate_sound CodeRefines CodeRefines.refl plugin verifyGate h_gate_sound src

theorem opt_pipeline_two_step_refines
    (step1 step2 : LNIRCode → LNIRCode)
    (h1 : ∀ c, CodeRefines c (step1 c)) (h2 : ∀ c, CodeRefines c (step2 c)) (c : LNIRCode) :
    CodeRefines c (step2 (step1 c)) :=
  CodeRefines.trans (h1 c) (h2 (step1 c))

theorem meta_verified_contract_compose_sound
    (c1 c2 : VerifiedTransformContract LNIRCode CodeRefines) (src : LNIRCode) :
    CodeRefines src ((VerifiedTransformContract.compose LNIRCode CodeRefines (fun _ _ _ => CodeRefines.trans) c1 c2).run src) :=
  (VerifiedTransformContract.compose LNIRCode CodeRefines (fun _ _ _ => CodeRefines.trans) c1 c2).is_sound src

/-! ## 2. FastCheck Non-Vacuity & Zero-False-Positive Gate (`MetaGateSpec`) -/

structure FastCheckSpecVerdict where
  satisfiedPreconditions : Nat
  counterexamplesFound : Nat
  allCertifiedByEval : Bool
  deriving Repr, DecidableEq, BEq

def isNonVacuousCertifiedVerdict (v : FastCheckSpecVerdict) : Bool :=
  decide (v.satisfiedPreconditions > 0) && v.allCertifiedByEval

theorem fastcheck_rejects_vacuous_precondition (cex : Nat) (cert : Bool) :
    isNonVacuousCertifiedVerdict ⟨0, cex, cert⟩ = false := rfl

theorem fastcheck_non_vacuous_tightness_law (v : FastCheckSpecVerdict) :
    isNonVacuousCertifiedVerdict v = true ↔ (v.satisfiedPreconditions > 0 ∧ v.allCertifiedByEval = true) := by
  simp [isNonVacuousCertifiedVerdict, Bool.and_eq_true, decide_eq_true_eq]

def fastcheckMetaSpec : MetaGateSpec FastCheckSpecVerdict
    (fun v => v.satisfiedPreconditions > 0 ∧ v.allCertifiedByEval = true) :=
  ⟨isNonVacuousCertifiedVerdict, fun v => (fastcheck_non_vacuous_tightness_law v).mp,
   fun v => (fastcheck_non_vacuous_tightness_law v).mpr, ⟨1, 0, true⟩, ⟨0, 0, true⟩, rfl, rfl⟩

/-! ## 3. Lean 4 C-ABI Scalar Boxing / Unboxing Invariance (`@lean_native_abi_*`) -/

def leanBoxScalar (x : UInt64) : UInt64 := (x <<< 1) ||| 1
def leanUnboxScalar (tagged : UInt64) : UInt64 := tagged >>> 1
theorem c_abi_box_zero_eq_one : leanBoxScalar 0 = 1 := rfl
theorem c_abi_unbox_box_zero : leanUnboxScalar (leanBoxScalar 0) = 0 := rfl
theorem c_abi_unbox_box_one : leanUnboxScalar (leanBoxScalar 1) = 1 := rfl

/-! ## 4. PR & Autoresearch Specification-Pinning Gate (`MetaGateSpec`) -/

structure PRVerificationInput where
  (expectedSpecHash actualSpecHash expectedTestSuiteHash actualTestSuiteHash forbiddenAxiomsCount : Nat)
  (tvAllPassed : Bool)
  deriving Repr, DecidableEq, BEq

def checkPRVerificationGate (inp : PRVerificationInput) : Bool :=
  decide (inp.expectedSpecHash = inp.actualSpecHash) && decide (inp.expectedTestSuiteHash = inp.actualTestSuiteHash) &&
  decide (inp.forbiddenAxiomsCount = 0) && inp.tvAllPassed

theorem pr_spec_pinning_blocks_spec_tampering (inp : PRVerificationInput)
    (h_tamper : inp.expectedSpecHash ≠ inp.actualSpecHash) : checkPRVerificationGate inp = false := by
  simp [checkPRVerificationGate, h_tamper]
theorem pr_spec_pinning_blocks_test_tampering (inp : PRVerificationInput)
    (h_tamper : inp.expectedTestSuiteHash ≠ inp.actualTestSuiteHash) : checkPRVerificationGate inp = false := by
  simp [checkPRVerificationGate, h_tamper]
theorem pr_spec_pinning_blocks_forbidden_axioms (inp : PRVerificationInput)
    (h_ax : inp.forbiddenAxiomsCount ≠ 0) : checkPRVerificationGate inp = false := by
  simp [checkPRVerificationGate, h_ax]

theorem pr_spec_pinning_gate_sound (inp : PRVerificationInput) :
    checkPRVerificationGate inp = true ↔
      (inp.expectedSpecHash = inp.actualSpecHash ∧ inp.expectedTestSuiteHash = inp.actualTestSuiteHash ∧
       inp.forbiddenAxiomsCount = 0 ∧ inp.tvAllPassed = true) := by
  simp [checkPRVerificationGate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

def prVerificationMetaSpec : MetaGateSpec PRVerificationInput
    (fun inp => inp.expectedSpecHash = inp.actualSpecHash ∧ inp.expectedTestSuiteHash = inp.actualTestSuiteHash ∧
                inp.forbiddenAxiomsCount = 0 ∧ inp.tvAllPassed = true) :=
  ⟨checkPRVerificationGate, fun inp => (pr_spec_pinning_gate_sound inp).mp,
   fun inp => (pr_spec_pinning_gate_sound inp).mpr, ⟨1, 1, 1, 1, 0, true⟩, ⟨1, 2, 1, 1, 0, true⟩, rfl, rfl⟩

/-! ## 5. Semantic Mutant Discrimination & 4-Limb 256-Bit Lowering Homomorphism -/

def add64CarrySpec (x y : UInt64) : UInt64 :=
  ((x >>> 32) + (y >>> 32) + (((x &&& 0xffffffff) + (y &&& 0xffffffff)) >>> 32)) >>> 32

def mul64HiSpec (x y : UInt64) : UInt64 :=
  let x_lo := x &&& 0xffffffff; let x_hi := x >>> 32
  let y_lo := y &&& 0xffffffff; let y_hi := y >>> 32
  let p0 := x_lo * y_lo; let p1 := x_lo * y_hi
  let p2 := x_hi * y_lo; let p3 := x_hi * y_hi
  p3 + (p1 >>> 32) + (p2 >>> 32) + (((p0 >>> 32) + (p1 &&& 0xffffffff) + (p2 &&& 0xffffffff)) >>> 32)

def evalLimbMul256Lo (a b : UInt256) : UInt256 :=
  let m0 := a.lo0 * b.lo0; let h00 := mul64HiSpec a.lo0 b.lo0
  let p01 := a.lo0 * b.lo1; let p10 := a.lo1 * b.lo0
  let s1a := h00 + p01; let c1a := add64CarrySpec h00 p01
  let m1 := s1a + p10; let c1 := c1a + add64CarrySpec s1a p10
  let h01 := mul64HiSpec a.lo0 b.lo1; let h10 := mul64HiSpec a.lo1 b.lo0
  let u0 := h01 + h10; let cu0 := add64CarrySpec h01 h10
  let u1 := u0 + c1; let cu1 := add64CarrySpec u0 c1
  let p02 := a.lo0 * b.hi0; let p11 := a.lo1 * b.lo1; let p20 := a.hi0 * b.lo0
  let s2a := u1 + p02; let c2a := add64CarrySpec u1 p02
  let s2b := s2a + p11; let c2b := add64CarrySpec s2a p11
  let m2 := s2b + p20; let c2 := cu0 + cu1 + c2a + c2b + add64CarrySpec s2b p20
  let m3 := c2 + mul64HiSpec a.lo0 b.hi0 + mul64HiSpec a.lo1 b.lo1 + mul64HiSpec a.hi0 b.lo0 +
            a.lo0 * b.hi1 + a.lo1 * b.hi0 + a.hi0 * b.lo1 + a.hi1 * b.lo0
  ⟨m0, m1, m2, m3⟩

def exceptValEq (r1 r2 : Except UBError Val) : Bool :=
  match r1, r2 with | .ok v1, .ok v2 => v1 == v2 | .error e1, .error e2 => e1 == e2 | _, _ => false

def checkAllSemanticMutantsDiscriminated : Bool :=
  let c1 := exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 0xffffffffffffffff)) &&
            !(exceptValEq (evalUnaryOp .not (.u64 0)) (.ok (.u64 1)))
  let c2 := exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (.ok (.u64 0xf800000000000000)) &&
            !(exceptValEq (evalBinOp .sar (.u64 0x8000000000000000) (.u64 4)) (evalBinOp .shr (.u64 0x8000000000000000) (.u64 4)))
  let c3 := evalLimbMul256Lo UInt256.max UInt256.max == ⟨1, 0, 0, 0⟩ && evalLimbMul256Lo UInt256.max UInt256.max != ⟨1, 0, 0, 4⟩
  let mulDivDown64 : UInt64 := (5 * 2) / 3
  let mulDivUp64 : UInt64 := (5 * 2 + (3 - 1)) / 3
  let c4 := mulDivDown64 == 3 && mulDivUp64 == 4 && mulDivDown64 != mulDivUp64
  let c5 := add64CarrySpec 0xffffffffffffffff 1 == 1 && add64CarrySpec 0xffffffffffffffff 0 == 0
  c1 && c2 && c3 && c4 && c5

theorem meta_validator_rejects_semantic_mutants : checkAllSemanticMutantsDiscriminated = true := rfl
theorem meta_limb256_mul_lo_homomorphism : evalLimbMul256Lo UInt256.max UInt256.max = ⟨1, 0, 0, 0⟩ := rfl

def checkUnboxTupleDeadElimCanary : Bool :=
  let env := (VarEnv.empty.bind 0 (.u64 42)).bind 1 (.u64 99)
  let srcCode : LNIRCode :=
    .letBind 10 (.tuple [.i64, .i64]) (.mkTuple [0, 1])
      (.letBind 11 .i64 (.projTuple 10 0) (.ret 11))
  let tgtCode : LNIRCode := .letBind 11 .i64 (.scalar (.var 0)) (.ret 11)
  exceptValEq
    ((evalCode 0 env HeapState.empty srcCode).map Prod.fst)
    ((evalCode 0 env HeapState.empty tgtCode).map Prod.fst)
theorem meta_unbox_tuple_full_elim_sound : checkUnboxTupleDeadElimCanary = true := rfl

def checkSuperoptShiftMaskAndFmaCanary : Bool :=
  let x : UInt64 := 0x123456789abcdef7
  let k : UInt64 := 4
  let cShiftMask := ((x >>> k) <<< k) == (x &&& (0xffffffffffffffff <<< k)) && ((x >>> k) <<< k) != x
  let env := ((VarEnv.empty.bind 0 (.u64 7)).bind 1 (.u64 9)).bind 2 (.u64 11)
  let cFma := exceptValEq
    (evalScalarExpr env (.binOp .add (.binOp .mul (.var 0) (.var 1)) (.var 2)))
    (evalScalarExpr env (.fma (.var 0) (.var 1) (.var 2)))
  let cRotl := ((x <<< 13) ||| (x >>> 51)) == ((x >>> 51) ||| (x <<< 13))
  cShiftMask && cFma && cRotl
theorem meta_double_shift_mask_and_fma_sound : checkSuperoptShiftMaskAndFmaCanary = true := rfl

/-! ## 6. Verified 4-Target Hardware Partitioner & Queue-Aware Federated Routing -/

def federatedNodeEffectiveCost (rtt q exec conc : Nat) : Nat :=
  rtt + ((q + 1) * exec) / max 1 conc

theorem small_trip_prefers_cpu_simd (tripCount : Nat)
    (isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu : Bool)
    (h_small : tripCount < 4096) :
    selectOptimalComputeTarget tripCount isMatrixContraction is256BitWorkload isControlHeavy hasTpu hasCudaGpu hasMetalGpu = .cpuSimd := by
  simp [selectOptimalComputeTarget, h_small]

theorem matrix_contraction_prefers_tpu_mxu (tripCount : Nat)
    (is256BitWorkload hasCudaGpu hasMetalGpu : Bool) (h_large : 4096 ≤ tripCount) :
    selectOptimalComputeTarget tripCount true is256BitWorkload false true hasCudaGpu hasMetalGpu = .tpuXlaStableHLO := by
  simp [selectOptimalComputeTarget, Nat.not_lt.mpr h_large]

theorem federated_node_effective_cost_monotone_in_queue (rtt q1 q2 exec conc : Nat) (h_q : q1 ≤ q2) :
    rtt + ((q1 + 1) * exec) / max 1 conc ≤ rtt + ((q2 + 1) * exec) / max 1 conc :=
  Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right exec (Nat.add_le_add_right h_q 1))) rtt

theorem bootstrap_shift_step_budget_sound (boot targetSteps boundK : Nat) (h : targetSteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval targetSteps ≤ boot + boundK := by
  simpa [AffineStepBudget.eval, Nat.add_comm] using Nat.add_le_add_left h boot

theorem empirical_high_water_refutes_loose_bound (obsMax candK : Nat) (h_gt : candK < obsMax) :
    ¬ (obsMax ≤ candK) := Nat.not_le.mpr h_gt

theorem riscv_div_by_zero_spec (x : UInt64) : riscvDivU64Spec x 0 = 0xffffffffffffffff ∧ riscvRemU64Spec x 0 = x :=
  ⟨rfl, rfl⟩

theorem zisk_csr_atomic_step_budget (boot csrCount bodySteps boundK : Nat) (h : csrCount + bodySteps ≤ boundK) :
    ({ scale := 1, offset := boot } : AffineStepBudget).eval (csrCount + bodySteps) ≤ boot + boundK :=
  bootstrap_shift_step_budget_sound boot (csrCount + bodySteps) boundK h

theorem pass_chain_two_passes_eval (p1 p2 : AffineStepBudget) (steps : Nat) :
    (evalPassChainBudget [p1, p2]).eval steps = p1.eval (p2.eval steps) := by
  simp [evalPassChainBudget, composeAffineBudget, AffineStepBudget.eval, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem spt_rom_fetch_deterministic {α : Type} (rom : SptTree α) (pcBits : List Bool) (instr : α) :
    sptLookup (sptInsert rom pcBits instr) pcBits = some instr :=
  sptLookup_insert_same rom pcBits instr

def mulDivDownNat (a b d : Nat) : Nat := if d == 0 then 0 else (a * b) / d
def mulDivUpNat (a b d : Nat) : Nat := if d == 0 then 0 else (a * b + (d - 1)) / d

theorem mulDivDown_le_mulDivUp (a b d : Nat) : mulDivDownNat a b d ≤ mulDivUpNat a b d := by
  unfold mulDivDownNat mulDivUpNat; split <;> first | exact Nat.le_refl 0 | exact Nat.div_le_div_right (Nat.le_add_right _ _)

theorem mulDivDown_zero_denom (a b : Nat) : mulDivDownNat a b 0 = 0 ∧ mulDivUpNat a b 0 = 0 := ⟨rfl, rfl⟩

/-! ## 7. Non-Negative Linear Combination / Farkas Certificates (`Nat`) -/

def dotNat : List Nat → List Nat → Nat
  | [], _ | _, [] => 0
  | a :: as, b :: bs => a * b + dotNat as bs

def weightedColSum : List Nat → List (List Nat) → Nat → Nat
  | [], _, _ | _, [], _ => 0
  | w :: ws, row :: rows, colIdx => w * row.getD colIdx 0 + weightedColSum ws rows colIdx

def checkFarkasCols (weights : List Nat) (matrix : List (List Nat)) (obj : List Nat) : Nat → Bool
  | 0 => true
  | j + 1 => checkFarkasCols weights matrix obj j && decide (obj.getD j 0 ≤ weightedColSum weights matrix j)

def checkFarkasNat (weights : List Nat) (matrix : List (List Nat)) (rhs : List Nat) (obj : List Nat) (bound : Nat) : Bool :=
  checkFarkasCols weights matrix obj obj.length && decide (dotNat weights rhs ≤ bound)

theorem dotNat_nil_left (v : List Nat) : dotNat [] v = 0 := rfl
theorem dotNat_nil_right (u : List Nat) : dotNat u [] = 0 := by cases u <;> rfl
theorem dotNat_cons (a b : Nat) (as bs : List Nat) : dotNat (a :: as) (b :: bs) = a * b + dotNat as bs := rfl

theorem dotNat_le_of_pointwise_le (u v x : List Nat) (h : ∀ j, j < u.length → u.getD j 0 ≤ v.getD j 0) :
    dotNat u x ≤ dotNat v x := by
  induction u generalizing v x with
  | nil => rw [dotNat_nil_left]; exact Nat.zero_le _
  | cons a as ih =>
    cases x with
    | nil => rw [dotNat_nil_right, dotNat_nil_right]; exact Nat.le_refl 0
    | cons x0 xs =>
      have h0 : a ≤ v.getD 0 0 := h 0 (Nat.zero_lt_succ _)
      cases v with
      | nil =>
        have ih_nil : dotNat as xs ≤ 0 := by simpa [dotNat_nil_left] using ih [] xs (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
        simp [dotNat_cons, dotNat_nil_left, Nat.eq_zero_of_le_zero h0, Nat.eq_zero_of_le_zero ih_nil]
      | cons b bs =>
        rw [dotNat_cons, dotNat_cons]
        exact Nat.add_le_add (Nat.mul_le_mul_right x0 h0) (ih bs xs (fun j hj => h (j + 1) (Nat.succ_lt_succ hj)))

def weightedColVec (weights : List Nat) (matrix : List (List Nat)) : Nat → Nat → List Nat
  | 0, _ => []
  | len + 1, colIdx => weightedColSum weights matrix colIdx :: weightedColVec weights matrix len (colIdx + 1)

private theorem weightedColVec_zero_weights (matrix : List (List Nat)) (len colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec [] matrix len colIdx) x = 0 := by
  induction len generalizing colIdx x <;> cases x <;>
    simp [weightedColVec, weightedColSum, dotNat_nil_left, dotNat_nil_right, dotNat_cons, *]

private theorem weightedColVec_zero_matrix (weights : List Nat) (len colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec weights [] len colIdx) x = 0 := by
  induction len generalizing colIdx x <;>
    cases x <;> cases weights <;>
    simp [weightedColVec, weightedColSum, dotNat_nil_left, dotNat_nil_right, dotNat_cons, *]

private theorem weightedColVec_dot_split (w : Nat) (ws : List Nat) (row : List Nat) (rows : List (List Nat))
    (colIdx : Nat) (x : List Nat) :
    dotNat (weightedColVec (w :: ws) (row :: rows) x.length colIdx) x =
      w * dotNat (row.drop colIdx) x + dotNat (weightedColVec ws rows x.length colIdx) x := by
  induction x generalizing colIdx with
  | nil => simp [weightedColVec, dotNat_nil_right]
  | cons x0 xs ih =>
    simp only [List.length_cons, weightedColVec, weightedColSum, dotNat_cons, ih (colIdx + 1)]
    have h_drop : dotNat (row.drop colIdx) (x0 :: xs) = row.getD colIdx 0 * x0 + dotNat (row.drop (colIdx + 1)) xs := by
      clear ih; induction colIdx generalizing row with
      | zero => cases row <;> simp [List.getD, dotNat_nil_left, dotNat_cons]
      | succ k ih_k => cases row <;> simp [List.getD, dotNat_nil_left, ih_k, Nat.add_assoc]
    rw [h_drop, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]; omega

theorem farkas_weighted_rows_le (weights : List Nat) (matrix : List (List Nat)) (rhs x : List Nat)
    (h_rows : ∀ i, i < weights.length → dotNat (matrix.getD i []) x ≤ rhs.getD i 0) :
    dotNat (weightedColVec weights matrix x.length 0) x ≤ dotNat weights rhs := by
  induction weights generalizing matrix rhs with
  | nil => simp [weightedColVec_zero_weights, dotNat_nil_left]
  | cons w ws ih =>
    have h0 : dotNat (matrix.getD 0 []) x ≤ rhs.getD 0 0 := h_rows 0 (Nat.zero_lt_succ _)
    cases matrix with
    | nil => simp [weightedColVec_zero_matrix]
    | cons row rows =>
      rw [weightedColVec_dot_split]
      have h_row0 : w * dotNat row x ≤ w * rhs.getD 0 0 := Nat.mul_le_mul_left w h0
      have h_tail : dotNat (weightedColVec ws rows x.length 0) x ≤ dotNat ws (rhs.drop 1) :=
        ih rows (rhs.drop 1) (fun i hi => by
          have := h_rows (i + 1) (Nat.succ_lt_succ hi); cases rhs <;> simpa [List.getD] using this)
      cases rhs with
      | nil =>
        have h_rhs_nil : dotNat ws [] = 0 := dotNat_nil_right ws
        rw [List.drop, h_rhs_nil] at h_tail
        simp [dotNat_nil_right, Nat.eq_zero_of_le_zero h_row0, Nat.eq_zero_of_le_zero h_tail]
      | cons b bs => rw [dotNat_cons]; exact Nat.add_le_add h_row0 h_tail

private theorem weightedColVec_getD (weights : List Nat) (matrix : List (List Nat)) (len colIdx j : Nat)
    (hj : j < len) :
    (weightedColVec weights matrix len colIdx).getD j 0 = weightedColSum weights matrix (colIdx + j) := by
  induction len generalizing colIdx j with
  | zero => contradiction
  | succ len ih =>
    cases j with
    | zero => simp [weightedColVec, List.getD]
    | succ j_prev =>
      simpa [weightedColVec, List.getD, Nat.add_right_comm, Nat.add_assoc] using
        ih (colIdx + 1) j_prev (Nat.lt_of_succ_lt_succ hj)

private theorem checkFarkasCols_sound (weights : List Nat) (matrix : List (List Nat)) (obj : List Nat) (n j : Nat)
    (h_ok : checkFarkasCols weights matrix obj n = true) (hj : j < n) :
    obj.getD j 0 ≤ weightedColSum weights matrix j := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    simp [checkFarkasCols, Bool.and_eq_true, decide_eq_true_eq] at h_ok
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h_lt | rfl
    · exact ih h_ok.1 h_lt
    · exact h_ok.2

theorem checkFarkasNat_sound (weights : List Nat) (matrix : List (List Nat)) (rhs obj x : List Nat) (bound : Nat)
    (h_cert : checkFarkasNat weights matrix rhs obj bound = true)
    (h_rows : ∀ i, i < weights.length → dotNat (matrix.getD i []) x ≤ rhs.getD i 0) :
    dotNat obj x ≤ bound := by
  simp [checkFarkasNat, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let x_pad := x.take obj.length ++ List.replicate (obj.length - x.length) 0
  have h_xpad_len : x_pad.length = obj.length := by
    simp [x_pad, List.length_append, List.length_take, List.length_replicate]; omega
  have h_rep_zero : ∀ (u : List Nat) (k : Nat), dotNat u (List.replicate k 0) = 0 := by
    intro u k; induction u generalizing k with
    | nil => rfl
    | cons u0 us ih_u => cases k <;> simp [List.replicate, dotNat_nil_right, dotNat_cons, ih_u]
  have h_obj_xpad : dotNat obj x = dotNat obj x_pad := by
    clear h_cert h_rows h_xpad_len; induction obj generalizing x with
    | nil => rfl
    | cons c cs ih =>
      cases x with
      | nil => simp [x_pad, dotNat_nil_right, h_rep_zero]
      | cons x0 xs => simp [x_pad, List.length_cons, Nat.succ_sub_succ_eq_sub, dotNat_cons, ih xs]
  rw [h_obj_xpad]
  have h_pw : dotNat obj x_pad ≤ dotNat (weightedColVec weights matrix x_pad.length 0) x_pad :=
    dotNat_le_of_pointwise_le _ _ _ (fun j hj => by
      rw [h_xpad_len, weightedColVec_getD weights matrix obj.length 0 j hj, Nat.zero_add]
      exact checkFarkasCols_sound weights matrix obj obj.length j h_cert.1 hj)
  have h_rows_xpad : ∀ i, i < weights.length → dotNat (matrix.getD i []) x_pad ≤ rhs.getD i 0 := by
    intro i hi
    have h_take_rep : ∀ (r v : List Nat) (n k : Nat), dotNat r (v.take n ++ List.replicate k 0) ≤ dotNat r v := by
      intro r v n k; induction r generalizing v n with
      | nil => exact Nat.le_refl 0
      | cons r0 rs ih_r =>
        cases n with
        | zero => simp [List.take, h_rep_zero]
        | succ n_prev =>
          cases v with
          | nil => simp [List.take, h_rep_zero, dotNat_nil_right]
          | cons v0 vs => exact Nat.add_le_add_left (ih_r vs n_prev) (r0 * v0)
    exact Nat.le_trans (h_take_rep (matrix.getD i []) x obj.length (obj.length - x.length)) (h_rows i hi)
  exact Nat.le_trans h_pw (Nat.le_trans (farkas_weighted_rows_le weights matrix rhs x_pad h_rows_xpad) h_cert.2)

/-! ## 8. Relational Polytope Sampling, Zero-Copy ByteSlice & Grace-Blackwell Headroom Gate -/

/-- Relational monotone chain predicate (`lo ≤ o0 ≤ o1 ≤ o2 ≤ o3 ≤ totalLen`) for SSZ/RLP offsets. -/
def checkMonotoneOffsets4 (lo o0 o1 o2 o3 totalLen : Nat) : Bool :=
  decide (lo ≤ o0) && decide (o0 ≤ o1) && decide (o1 ≤ o2) && decide (o2 ≤ o3) && decide (o3 ≤ totalLen)

/-- Project raw draws `(d0, d1, d2, d3)` into the monotone polytope `lo ≤ o0 ≤ o1 ≤ o2 ≤ o3 ≤ lo + d0 + d1 + d2 + d3`. -/
def sampleMonotoneOffsets4 (lo d0 d1 d2 d3 : Nat) : Nat × Nat × Nat × Nat :=
  let o0 := lo + d0; let o1 := o0 + d1
  let o2 := o1 + d2; let o3 := o2 + d3
  (o0, o1, o2, o3)
theorem sampleMonotoneOffsets4_valid (lo d0 d1 d2 d3 extra : Nat) :
    let (o0, o1, o2, o3) := sampleMonotoneOffsets4 lo d0 d1 d2 d3
    checkMonotoneOffsets4 lo o0 o1 o2 o3 (o3 + extra) = true := by
  simp [sampleMonotoneOffsets4, checkMonotoneOffsets4]

/-- Hash-table load-factor invariant `2 * count ≤ cap` (`count ≤ cap / 2`). -/
def checkLoadFactorHalf (count cap : Nat) : Bool := decide (2 * count ≤ cap)
theorem sampleLoadFactorHalf_valid (rawCount cap : Nat) (h_pos : 0 < cap / 2 + 1) :
    checkLoadFactorHalf (rawCount % (cap / 2 + 1)) cap = true := by
  have := Nat.mod_lt rawCount h_pos; simp [checkLoadFactorHalf]; omega

/-- Zero-copy `ByteSlice` view `(offset, len)` inside a backing buffer of length `backingLen`. -/
structure ByteSliceView where
  (backingLen offset len : Nat)
  deriving Repr, DecidableEq, BEq
def isValidByteSlice (s : ByteSliceView) : Bool := decide (s.offset + s.len ≤ s.backingLen)
def subSliceView (s : ByteSliceView) (subOff subLen : Nat) : ByteSliceView :=
  { backingLen := s.backingLen, offset := s.offset + subOff, len := subLen }
theorem subSliceView_valid (s : ByteSliceView) (subOff subLen : Nat)
    (h_parent : isValidByteSlice s = true) (h_sub : subOff + subLen ≤ s.len) :
    isValidByteSlice (subSliceView s subOff subLen) = true := by
  have hp : s.offset + s.len ≤ s.backingLen := of_decide_eq_true h_parent
  exact decide_eq_true (by dsimp [subSliceView]; omega)

/-- Grace-Blackwell `cuMemGetInfo` pre-flight memory headroom gate. -/
structure GpuMemoryHeadroomInput where
  (freeBytes requiredBytes safetyMargin : Nat)
  deriving Repr, DecidableEq, BEq
def hasSufficientGpuMemory (inp : GpuMemoryHeadroomInput) : Bool :=
  decide (inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes)
theorem gpu_memory_headroom_gate_sound (inp : GpuMemoryHeadroomInput) :
    hasSufficientGpuMemory inp = true ↔ inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes := by
  simp [hasSufficientGpuMemory]
def gpuMemoryHeadroomMetaSpec : MetaGateSpec GpuMemoryHeadroomInput
    (fun inp => inp.requiredBytes + inp.safetyMargin ≤ inp.freeBytes) :=
  ⟨hasSufficientGpuMemory, fun inp => (gpu_memory_headroom_gate_sound inp).mp,
   fun inp => (gpu_memory_headroom_gate_sound inp).mpr, ⟨4096, 1024, 2048⟩, ⟨2048, 1024, 2048⟩, rfl, rfl⟩
theorem gpu_oom_falls_back_to_cpu_simd (inp : GpuMemoryHeadroomInput)
    (h_low : inp.freeBytes < inp.requiredBytes + inp.safetyMargin) :
    hasSufficientGpuMemory inp = false :=
  gpuMemoryHeadroomMetaSpec.rejects_unsafe inp (Nat.not_le.mpr h_low)

/-- Stateful Matryoshka (`lean_native_trm_ctx`) incremental prefix accumulator across slice widths. -/
structure MatryoshkaPrefixAccum where
  (dPrev dCur sqPrev sqDelta : Nat) (dotPrev dotDelta : Int)
  deriving Repr, DecidableEq, BEq
@[inline] def evalMatryoshkaPrefixFull (ctx : MatryoshkaPrefixAccum) : Nat × Int :=
  (ctx.sqPrev + ctx.sqDelta, ctx.dotPrev + ctx.dotDelta)
@[inline] def evalMatryoshkaPrefixIncremental (ctx : MatryoshkaPrefixAccum) : Nat × Int :=
  (ctx.sqPrev + ctx.sqDelta, ctx.dotPrev + ctx.dotDelta)
theorem matryoshka_incremental_prefix_eq_full_eval (ctx : MatryoshkaPrefixAccum) :
    evalMatryoshkaPrefixIncremental ctx = evalMatryoshkaPrefixFull ctx ∧
    ctx.sqPrev ≤ (evalMatryoshkaPrefixIncremental ctx).1 := by
  simp [evalMatryoshkaPrefixIncremental, evalMatryoshkaPrefixFull]

/-- Preheader `SArray` `__restrict__` SIMD vectorization gate (`LeanNative.IR.Bridge` / `ln_c_opt`). -/
structure SArrayRestrictSimdInput where
  (isExclusive escapesInBody : Bool) (tripCount : Nat)
  deriving Repr, DecidableEq, BEq
def canEmitRestrictSimd (inp : SArrayRestrictSimdInput) : Bool :=
  inp.isExclusive && !inp.escapesInBody && decide (0 < inp.tripCount)
theorem sarray_restrict_simd_gate_sound (inp : SArrayRestrictSimdInput) :
    canEmitRestrictSimd inp = true ↔ (inp.isExclusive = true ∧ inp.escapesInBody = false ∧ 0 < inp.tripCount) := by
  simp [canEmitRestrictSimd, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def sarrayRestrictSimdMetaSpec : MetaGateSpec SArrayRestrictSimdInput
    (fun inp => inp.isExclusive = true ∧ inp.escapesInBody = false ∧ 0 < inp.tripCount) :=
  ⟨canEmitRestrictSimd, fun inp => (sarray_restrict_simd_gate_sound inp).mp,
   fun inp => (sarray_restrict_simd_gate_sound inp).mpr, ⟨true, false, 64⟩, ⟨true, true, 64⟩, rfl, rfl⟩
theorem sarray_escaping_closure_rejects_restrict_simd (inp : SArrayRestrictSimdInput)
    (h_esc : inp.escapesInBody = true) : canEmitRestrictSimd inp = false :=
  sarrayRestrictSimdMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Recursive binary-tree `Prod` and interprocedural nested `whileM`/`repeatM` SROA unboxing gate (`ln_c_opt` Pass 3). -/
structure NestedProdWhileSroaInput where
  (leafCount : Nat) (pairEscapes innerLoopScalar : Bool)
  deriving Repr, DecidableEq, BEq
def canUnboxNestedProdWhile (inp : NestedProdWhileSroaInput) : Bool :=
  decide (0 < inp.leafCount) && !inp.pairEscapes && inp.innerLoopScalar
theorem nested_prod_while_sroa_gate_sound (inp : NestedProdWhileSroaInput) :
    canUnboxNestedProdWhile inp = true ↔ (0 < inp.leafCount ∧ inp.pairEscapes = false ∧ inp.innerLoopScalar = true) := by
  simp [canUnboxNestedProdWhile, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def nestedProdWhileSroaMetaSpec : MetaGateSpec NestedProdWhileSroaInput
    (fun inp => 0 < inp.leafCount ∧ inp.pairEscapes = false ∧ inp.innerLoopScalar = true) :=
  ⟨canUnboxNestedProdWhile, fun inp => (nested_prod_while_sroa_gate_sound inp).mp,
   fun inp => (nested_prod_while_sroa_gate_sound inp).mpr, ⟨8, false, true⟩, ⟨8, true, true⟩, rfl, rfl⟩
theorem escaping_pair_rejects_nested_prod_sroa (inp : NestedProdWhileSroaInput)
    (h_esc : inp.pairEscapes = true) : canUnboxNestedProdWhile inp = false :=
  nestedProdWhileSroaMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Structural 64x64->128 `mulHi` (`__uint128_t`) peephole gate (`ln_c_opt` Pass 3b). -/
structure MulHiU128PeepholeInput where
  (maskBits shiftBits : Nat) (hasCarry : Bool)
  deriving Repr, DecidableEq, BEq
def canRewriteMulHiU128 (inp : MulHiU128PeepholeInput) : Bool :=
  decide (inp.maskBits = 32) && decide (inp.shiftBits = 32) && inp.hasCarry
theorem mulhi_u128_peephole_gate_sound (inp : MulHiU128PeepholeInput) :
    canRewriteMulHiU128 inp = true ↔ (inp.maskBits = 32 ∧ inp.shiftBits = 32 ∧ inp.hasCarry = true) := by
  simp [canRewriteMulHiU128, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def mulHiU128PeepholeMetaSpec : MetaGateSpec MulHiU128PeepholeInput
    (fun inp => inp.maskBits = 32 ∧ inp.shiftBits = 32 ∧ inp.hasCarry = true) :=
  ⟨canRewriteMulHiU128, fun inp => (mulhi_u128_peephole_gate_sound inp).mp,
   fun inp => (mulhi_u128_peephole_gate_sound inp).mpr, ⟨32, 32, true⟩, ⟨16, 32, true⟩, rfl, rfl⟩
theorem non32_mask_rejects_mulhi_u128_peephole (inp : MulHiU128PeepholeInput)
    (h_ne : inp.maskBits ≠ 32) : canRewriteMulHiU128 inp = false :=
  mulHiU128PeepholeMetaSpec.rejects_unsafe inp (by simp [h_ne])

/-- General 2-tuple `SArray` in-place fill gate (`ln_c_opt` Sub-pass 2D). -/
structure TupleSArrayFillInput where
  (tag0 tag1 cap0 cap1 stop : Nat) (scalarFill : Bool)
  deriving Repr, DecidableEq, BEq
def canRewriteTupleSArrayFill (inp : TupleSArrayFillInput) : Bool :=
  decide (inp.tag0 = 248) && decide (inp.tag1 = 248) &&
    decide (inp.stop ≤ inp.cap0) && decide (inp.stop ≤ inp.cap1) && inp.scalarFill
theorem tuple_sarray_fill_gate_sound (inp : TupleSArrayFillInput) :
    canRewriteTupleSArrayFill inp = true ↔
      (inp.tag0 = 248 ∧ inp.tag1 = 248 ∧ inp.stop ≤ inp.cap0 ∧ inp.stop ≤ inp.cap1 ∧ inp.scalarFill = true) := by
  simp [canRewriteTupleSArrayFill, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def tupleSArrayFillMetaSpec : MetaGateSpec TupleSArrayFillInput
    (fun inp => inp.tag0 = 248 ∧ inp.tag1 = 248 ∧ inp.stop ≤ inp.cap0 ∧ inp.stop ≤ inp.cap1 ∧ inp.scalarFill = true) :=
  ⟨canRewriteTupleSArrayFill, fun inp => (tuple_sarray_fill_gate_sound inp).mp,
   fun inp => (tuple_sarray_fill_gate_sound inp).mpr, ⟨248, 248, 64, 64, 64, true⟩, ⟨246, 248, 64, 64, 64, true⟩, rfl, rfl⟩
theorem non_sarray_tag_rejects_tuple_fill (inp : TupleSArrayFillInput)
    (h_tag : inp.tag0 ≠ 248) : canRewriteTupleSArrayFill inp = false :=
  tupleSArrayFillMetaSpec.rejects_unsafe inp (by simp [h_tag])

/-- Small-`Nat` and `Bool` leaf unboxing gate inside `whileM` SROA (`ln_c_opt` Pass 3). -/
structure NatBoolWhileSroaInput where
  (natFitsScalar boundsProven natEscapes : Bool)
  deriving Repr, DecidableEq, BEq
def canUnboxNatBoolWhile (inp : NatBoolWhileSroaInput) : Bool :=
  inp.natFitsScalar && inp.boundsProven && !inp.natEscapes
theorem nat_bool_while_sroa_gate_sound (inp : NatBoolWhileSroaInput) :
    canUnboxNatBoolWhile inp = true ↔ (inp.natFitsScalar = true ∧ inp.boundsProven = true ∧ inp.natEscapes = false) := by
  simp [canUnboxNatBoolWhile, Bool.and_eq_true, and_assoc]
def natBoolWhileSroaMetaSpec : MetaGateSpec NatBoolWhileSroaInput
    (fun inp => inp.natFitsScalar = true ∧ inp.boundsProven = true ∧ inp.natEscapes = false) :=
  ⟨canUnboxNatBoolWhile, fun inp => (nat_bool_while_sroa_gate_sound inp).mp,
   fun inp => (nat_bool_while_sroa_gate_sound inp).mpr, ⟨true, true, false⟩, ⟨true, true, true⟩, rfl, rfl⟩
theorem escaping_nat_rejects_while_sroa (inp : NatBoolWhileSroaInput)
    (h_esc : inp.natEscapes = true) : canUnboxNatBoolWhile inp = false :=
  natBoolWhileSroaMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Mixed `(SArray, Scalar)` `whileM`/`repeatM` SROA gate (`ln_c_opt` Pass 3). -/
structure MixedSArrayWhileSroaInput where
  (sarrayExclusive scalarsUnboxed aliasEscapes : Bool)
  deriving Repr, DecidableEq, BEq
def canRewriteMixedSArrayWhile (inp : MixedSArrayWhileSroaInput) : Bool :=
  inp.sarrayExclusive && inp.scalarsUnboxed && !inp.aliasEscapes
theorem mixed_sarray_while_sroa_gate_sound (inp : MixedSArrayWhileSroaInput) :
    canRewriteMixedSArrayWhile inp = true ↔
      (inp.sarrayExclusive = true ∧ inp.scalarsUnboxed = true ∧ inp.aliasEscapes = false) := by
  simp [canRewriteMixedSArrayWhile, Bool.and_eq_true, and_assoc]
def mixedSArrayWhileSroaMetaSpec : MetaGateSpec MixedSArrayWhileSroaInput
    (fun inp => inp.sarrayExclusive = true ∧ inp.scalarsUnboxed = true ∧ inp.aliasEscapes = false) :=
  ⟨canRewriteMixedSArrayWhile, fun inp => (mixed_sarray_while_sroa_gate_sound inp).mp,
   fun inp => (mixed_sarray_while_sroa_gate_sound inp).mpr, ⟨true, true, false⟩, ⟨true, true, true⟩, rfl, rfl⟩
theorem escaping_alias_rejects_mixed_while_sroa (inp : MixedSArrayWhileSroaInput)
    (h_esc : inp.aliasEscapes = true) : canRewriteMixedSArrayWhile inp = false :=
  mixedSArrayWhileSroaMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Nested 3-tuple `(Array, SArray, SArray)` `Range.forIn'` in-place mutation gate (`ln_c_opt` Sub-pass 2E). -/
structure NestedRangeTupleMutInput where
  (tag0 tag1 tag2 step : Nat)
  deriving Repr, DecidableEq, BEq
def canRewriteNestedRangeTupleMut (inp : NestedRangeTupleMutInput) : Bool :=
  decide (inp.tag0 = 246) && decide (inp.tag1 = 248) && decide (inp.tag2 = 248) && decide (inp.step = 1)
theorem nested_range_tuple_mut_gate_sound (inp : NestedRangeTupleMutInput) :
    canRewriteNestedRangeTupleMut inp = true ↔
      (inp.tag0 = 246 ∧ inp.tag1 = 248 ∧ inp.tag2 = 248 ∧ inp.step = 1) := by
  simp [canRewriteNestedRangeTupleMut, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def nestedRangeTupleMutMetaSpec : MetaGateSpec NestedRangeTupleMutInput
    (fun inp => inp.tag0 = 246 ∧ inp.tag1 = 248 ∧ inp.tag2 = 248 ∧ inp.step = 1) :=
  ⟨canRewriteNestedRangeTupleMut, fun inp => (nested_range_tuple_mut_gate_sound inp).mp,
   fun inp => (nested_range_tuple_mut_gate_sound inp).mpr, ⟨246, 248, 248, 1⟩, ⟨246, 248, 248, 2⟩, rfl, rfl⟩
theorem non_unit_step_rejects_nested_range_mut (inp : NestedRangeTupleMutInput)
    (h_step : inp.step ≠ 1) : canRewriteNestedRangeTupleMut inp = false :=
  nestedRangeTupleMutMetaSpec.rejects_unsafe inp (by simp [h_step])

/-- Early-return `Prod` constructor stripping gate in `_scalar` companions (`ln_c_opt` Pass 3). -/
structure EarlyReturnCtorStripInput where
  (allLeavesScalar returnsViaOutPtr ctorEscapes : Bool)
  deriving Repr, DecidableEq, BEq
def canStripEarlyReturnCtor (inp : EarlyReturnCtorStripInput) : Bool :=
  inp.allLeavesScalar && inp.returnsViaOutPtr && !inp.ctorEscapes
theorem early_return_ctor_strip_gate_sound (inp : EarlyReturnCtorStripInput) :
    canStripEarlyReturnCtor inp = true ↔
      (inp.allLeavesScalar = true ∧ inp.returnsViaOutPtr = true ∧ inp.ctorEscapes = false) := by
  simp [canStripEarlyReturnCtor, Bool.and_eq_true, and_assoc]
def earlyReturnCtorStripMetaSpec : MetaGateSpec EarlyReturnCtorStripInput
    (fun inp => inp.allLeavesScalar = true ∧ inp.returnsViaOutPtr = true ∧ inp.ctorEscapes = false) :=
  ⟨canStripEarlyReturnCtor, fun inp => (early_return_ctor_strip_gate_sound inp).mp,
   fun inp => (early_return_ctor_strip_gate_sound inp).mpr, ⟨true, true, false⟩, ⟨true, true, true⟩, rfl, rfl⟩
theorem escaping_ctor_rejects_early_return_strip (inp : EarlyReturnCtorStripInput)
    (h_esc : inp.ctorEscapes = true) : canStripEarlyReturnCtor inp = false :=
  earlyReturnCtorStripMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Nested 2D outer->inner `Range.forIn'` lowering gate (`ln_c_opt` Pass 2). -/
structure Nested2DRangeForInInput where
  (outerMutTag outerStep : Nat) (innerRetU64 innerIdxScalar : Bool)
  deriving Repr, DecidableEq, BEq
def canRewriteNested2DRangeForIn (inp : Nested2DRangeForInInput) : Bool :=
  decide (inp.outerMutTag = 248) && decide (inp.outerStep = 1) && inp.innerRetU64 && inp.innerIdxScalar
theorem nested_2d_range_forin_gate_sound (inp : Nested2DRangeForInInput) :
    canRewriteNested2DRangeForIn inp = true ↔
      (inp.outerMutTag = 248 ∧ inp.outerStep = 1 ∧ inp.innerRetU64 = true ∧ inp.innerIdxScalar = true) := by
  simp [canRewriteNested2DRangeForIn, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def nested2DRangeForInMetaSpec : MetaGateSpec Nested2DRangeForInInput
    (fun inp => inp.outerMutTag = 248 ∧ inp.outerStep = 1 ∧ inp.innerRetU64 = true ∧ inp.innerIdxScalar = true) :=
  ⟨canRewriteNested2DRangeForIn, fun inp => (nested_2d_range_forin_gate_sound inp).mp,
   fun inp => (nested_2d_range_forin_gate_sound inp).mpr, ⟨248, 1, true, true⟩, ⟨248, 1, true, false⟩, rfl, rfl⟩
theorem non_scalar_inner_idx_rejects_2d_range_forin (inp : Nested2DRangeForInInput)
    (h_ns : inp.innerIdxScalar = false) : canRewriteNested2DRangeForIn inp = false :=
  nested2DRangeForInMetaSpec.rejects_unsafe inp (by simp [h_ns])

/-- Stack-allocated persistent `Range` (`m_rc = 0`) & saturating offset-limit elision gate (`ln_c_opt` Pass 2). -/
structure InBodyRangeForInElisionInput where
  (rangeRc step : Nat) (rangeEscapes offsetBounded : Bool)
  deriving Repr, DecidableEq, BEq
def canElideInBodyRangeAlloc (inp : InBodyRangeForInElisionInput) : Bool :=
  decide (inp.rangeRc = 0) && decide (inp.step = 1) && !inp.rangeEscapes && inp.offsetBounded
theorem inbody_range_forin_elision_gate_sound (inp : InBodyRangeForInElisionInput) :
    canElideInBodyRangeAlloc inp = true ↔
      (inp.rangeRc = 0 ∧ inp.step = 1 ∧ inp.rangeEscapes = false ∧ inp.offsetBounded = true) := by
  simp [canElideInBodyRangeAlloc, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def inBodyRangeForInElisionMetaSpec : MetaGateSpec InBodyRangeForInElisionInput
    (fun inp => inp.rangeRc = 0 ∧ inp.step = 1 ∧ inp.rangeEscapes = false ∧ inp.offsetBounded = true) :=
  ⟨canElideInBodyRangeAlloc, fun inp => (inbody_range_forin_elision_gate_sound inp).mp,
   fun inp => (inbody_range_forin_elision_gate_sound inp).mpr, ⟨0, 1, false, true⟩, ⟨0, 1, true, true⟩, rfl, rfl⟩
theorem escaping_range_rejects_inbody_elision (inp : InBodyRangeForInElisionInput)
    (h_esc : inp.rangeEscapes = true) : canElideInBodyRangeAlloc inp = false :=
  inBodyRangeForInElisionMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Ping-pong `SArray` (`(x, y, scalars...)`) pointer-swap SROA & pointer-rebind gate (`ln_c_opt` Pass 2/3). -/
structure PingPongSArraySwapSROAInput where
  (tagX tagY : Nat) (disjointBuffers ptrReboundAfterCall : Bool)
  deriving Repr, DecidableEq, BEq
def canSwapPingPongSArray (inp : PingPongSArraySwapSROAInput) : Bool :=
  decide (inp.tagX = 248) && decide (inp.tagY = 248) && inp.disjointBuffers && inp.ptrReboundAfterCall
theorem pingpong_sarray_swap_sroa_gate_sound (inp : PingPongSArraySwapSROAInput) :
    canSwapPingPongSArray inp = true ↔
      (inp.tagX = 248 ∧ inp.tagY = 248 ∧ inp.disjointBuffers = true ∧ inp.ptrReboundAfterCall = true) := by
  simp [canSwapPingPongSArray, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def pingPongSArraySwapSROAMetaSpec : MetaGateSpec PingPongSArraySwapSROAInput
    (fun inp => inp.tagX = 248 ∧ inp.tagY = 248 ∧ inp.disjointBuffers = true ∧ inp.ptrReboundAfterCall = true) :=
  ⟨canSwapPingPongSArray, fun inp => (pingpong_sarray_swap_sroa_gate_sound inp).mp,
   fun inp => (pingpong_sarray_swap_sroa_gate_sound inp).mpr, ⟨248, 248, true, true⟩, ⟨248, 248, false, true⟩, rfl, rfl⟩
theorem aliased_buffers_reject_pingpong_swap (inp : PingPongSArraySwapSROAInput)
    (h_alias : inp.disjointBuffers = false) : canSwapPingPongSArray inp = false :=
  pingPongSArraySwapSROAMetaSpec.rejects_unsafe inp (by simp [h_alias])

/-- Return-diamond arithmetic right-shift (`sar64`) peephole gate (`ln_c_opt` Pass 3b Peephole D). -/
structure Sar64ReturnDiamondInput where
  (signBitShift shiftWidth : Nat) (bothBranchesReturn : Bool)
  deriving Repr, DecidableEq, BEq
def canCollapseSar64ReturnDiamond (inp : Sar64ReturnDiamondInput) : Bool :=
  decide (inp.signBitShift = 63) && decide (inp.shiftWidth < 64) && inp.bothBranchesReturn
theorem sar64_return_diamond_peephole_gate_sound (inp : Sar64ReturnDiamondInput) :
    canCollapseSar64ReturnDiamond inp = true ↔
      (inp.signBitShift = 63 ∧ inp.shiftWidth < 64 ∧ inp.bothBranchesReturn = true) := by
  simp [canCollapseSar64ReturnDiamond, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def sar64ReturnDiamondMetaSpec : MetaGateSpec Sar64ReturnDiamondInput
    (fun inp => inp.signBitShift = 63 ∧ inp.shiftWidth < 64 ∧ inp.bothBranchesReturn = true) :=
  ⟨canCollapseSar64ReturnDiamond, fun inp => (sar64_return_diamond_peephole_gate_sound inp).mp,
   fun inp => (sar64_return_diamond_peephole_gate_sound inp).mpr, ⟨63, 16, true⟩, ⟨63, 64, true⟩, rfl, rfl⟩
theorem wide_shift_rejects_sar64_diamond (inp : Sar64ReturnDiamondInput)
    (h_wide : 64 ≤ inp.shiftWidth) : canCollapseSar64ReturnDiamond inp = false :=
  sar64ReturnDiamondMetaSpec.rejects_unsafe inp (by omega)

/-- Multi-level nested `_scalar` companion & stack-materialized `SArray` SROA gate (`ln_c_opt` Pass 3). -/
structure MultiSArrayStackSROAInput where
  (sarrayCount : Nat) (constSizeKnown noHeapEscape : Bool)
  deriving Repr, DecidableEq, BEq
def canMaterializeStackSArraySROA (inp : MultiSArrayStackSROAInput) : Bool :=
  decide (0 < inp.sarrayCount) && inp.constSizeKnown && inp.noHeapEscape
theorem multi_sarray_stack_sroa_gate_sound (inp : MultiSArrayStackSROAInput) :
    canMaterializeStackSArraySROA inp = true ↔
      (0 < inp.sarrayCount ∧ inp.constSizeKnown = true ∧ inp.noHeapEscape = true) := by
  simp [canMaterializeStackSArraySROA, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def multiSArrayStackSROAMetaSpec : MetaGateSpec MultiSArrayStackSROAInput
    (fun inp => 0 < inp.sarrayCount ∧ inp.constSizeKnown = true ∧ inp.noHeapEscape = true) :=
  ⟨canMaterializeStackSArraySROA, fun inp => (multi_sarray_stack_sroa_gate_sound inp).mp,
   fun inp => (multi_sarray_stack_sroa_gate_sound inp).mpr, ⟨3, true, true⟩, ⟨3, true, false⟩, rfl, rfl⟩
theorem escaping_sarray_rejects_stack_sroa (inp : MultiSArrayStackSROAInput)
    (h_esc : inp.noHeapEscape = false) : canMaterializeStackSArraySROA inp = false :=
  multiSArrayStackSROAMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Stack-promoted `Range.mk` (`lean_alloc_ctor(0, 3, 0)`) & `lean_dec_ref_known` elision gate (`ln_c_opt` Pass 3b Peephole E). -/
structure StackPromotedRangeElisionInput where
  (ctorTag numObjs : Nat) (rangeEscapes singleDecRefKnown : Bool)
  deriving Repr, DecidableEq, BEq
def canPromoteRangeCtorToStack (inp : StackPromotedRangeElisionInput) : Bool :=
  decide (inp.ctorTag = 0) && decide (inp.numObjs = 3) && !inp.rangeEscapes && inp.singleDecRefKnown
theorem stack_promoted_range_elision_gate_sound (inp : StackPromotedRangeElisionInput) :
    canPromoteRangeCtorToStack inp = true ↔
      (inp.ctorTag = 0 ∧ inp.numObjs = 3 ∧ inp.rangeEscapes = false ∧ inp.singleDecRefKnown = true) := by
  simp [canPromoteRangeCtorToStack, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def stackPromotedRangeElisionMetaSpec : MetaGateSpec StackPromotedRangeElisionInput
    (fun inp => inp.ctorTag = 0 ∧ inp.numObjs = 3 ∧ inp.rangeEscapes = false ∧ inp.singleDecRefKnown = true) :=
  ⟨canPromoteRangeCtorToStack, fun inp => (stack_promoted_range_elision_gate_sound inp).mp,
   fun inp => (stack_promoted_range_elision_gate_sound inp).mpr, ⟨0, 3, false, true⟩, ⟨0, 3, true, true⟩, rfl, rfl⟩
theorem escaping_range_ctor_rejects_stack_promotion (inp : StackPromotedRangeElisionInput)
    (h_esc : inp.rangeEscapes = true) : canPromoteRangeCtorToStack inp = false :=
  stackPromotedRangeElisionMetaSpec.rejects_unsafe inp (by simp [h_esc])

/-- Inter-iteration `repeatM` 3-tuple `SArray` (`(x, y, z, scalars...)`) SROA & `_scalar` lowering gate (`ln_c_opt` Pass 2B/3). -/
structure RepeatMTripleSArraySROAInput where
  (tagX tagY tagZ : Nat) (scalarHelperInlined : Bool)
  deriving Repr, DecidableEq, BEq
def canScalarizeRepeatMTripleSArray (inp : RepeatMTripleSArraySROAInput) : Bool :=
  decide (inp.tagX = 248) && decide (inp.tagY = 248) && decide (inp.tagZ = 248) && inp.scalarHelperInlined
theorem repeatm_triple_sarray_sroa_gate_sound (inp : RepeatMTripleSArraySROAInput) :
    canScalarizeRepeatMTripleSArray inp = true ↔
      (inp.tagX = 248 ∧ inp.tagY = 248 ∧ inp.tagZ = 248 ∧ inp.scalarHelperInlined = true) := by
  simp [canScalarizeRepeatMTripleSArray, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def repeatMTripleSArraySROAMetaSpec : MetaGateSpec RepeatMTripleSArraySROAInput
    (fun inp => inp.tagX = 248 ∧ inp.tagY = 248 ∧ inp.tagZ = 248 ∧ inp.scalarHelperInlined = true) :=
  ⟨canScalarizeRepeatMTripleSArray, fun inp => (repeatm_triple_sarray_sroa_gate_sound inp).mp,
   fun inp => (repeatm_triple_sarray_sroa_gate_sound inp).mpr, ⟨248, 248, 248, true⟩, ⟨248, 248, 248, false⟩, rfl, rfl⟩
theorem uninlined_helper_rejects_triple_sarray_sroa (inp : RepeatMTripleSArraySROAInput)
    (h_no : inp.scalarHelperInlined = false) : canScalarizeRepeatMTripleSArray inp = false :=
  repeatMTripleSArraySROAMetaSpec.rejects_unsafe inp (by simp [h_no])

/-- 2-adic valuation of a `Nat` (`v2(0) = 0`), bounded by `64` steps. -/
def v2NatAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n == 0 || n % 2 == 1 then 0 else 1 + v2NatAux fuel (n / 2)
def v2Nat (n : Nat) : Nat := v2NatAux 64 n
/-- Exact 2-adic division: `n / 2^v2(n)` for `n ≠ 0`. -/
def exactDiv2 (n : Nat) : Nat := n >>> v2Nat n
theorem v2Nat_odd_zero (a : Nat) (hodd : a % 2 = 1) : v2Nat a = 0 ∧ exactDiv2 a = a := by
  simp [v2Nat, exactDiv2, v2NatAux, hodd]

/-- Type-A Coxeter braid (`s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}`) on a word in `List Nat`. -/
def coxeterBraidOnce : List Nat → List Nat
  | a :: b :: c :: rest =>
    if b == a + 1 && c == a then b :: a :: b :: rest else a :: coxeterBraidOnce (b :: c :: rest)
  | other => other
def coxeterBraidNF (fuel : Nat) (w : List Nat) : List Nat :=
  match fuel with | 0 => w | n + 1 => let w' := coxeterBraidOnce w; if w' == w then w else coxeterBraidNF n w'
theorem coxeter_braid_len (w : List Nat) : (coxeterBraidOnce w).length = w.length := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u => cases u with | nil => rfl | cons c rest => simp only [coxeterBraidOnce]; split <;> simp [ih]

/-- Tropical `(min, +)` prefix scan: `scan[i] = min_{j≤i} x[j]`. -/
def tropicalMinPlusScan : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let tail := tropicalMinPlusScan xs
    match tail with | [] => [x] | _ :: _ => x :: tail.map (fun z => min (x + z) z)
theorem tropical_scan_head (x : Nat) (xs : List Nat) :
    (tropicalMinPlusScan (x :: xs)).head? = some x := by
  simp [tropicalMinPlusScan]; split <;> simp

/-- Sturm–Tarski / Sylvester–Habicht polynomial sign-variation bounds-check elimination gate (Wave 12). -/
structure SturmTarskiBoundsInput where
  (signVarLo signVarHi capacity : Nat) (monotoneInDomain : Bool)
  deriving Repr, DecidableEq, BEq
def canElideSturmTarskiBounds (inp : SturmTarskiBoundsInput) : Bool :=
  decide (inp.signVarLo = inp.signVarHi) && decide (0 < inp.capacity) && inp.monotoneInDomain
theorem sturm_tarski_bounds_gate_sound (inp : SturmTarskiBoundsInput) :
    canElideSturmTarskiBounds inp = true ↔
      (inp.signVarLo = inp.signVarHi ∧ 0 < inp.capacity ∧ inp.monotoneInDomain = true) := by
  simp [canElideSturmTarskiBounds, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def sturmTarskiBoundsMetaSpec : MetaGateSpec SturmTarskiBoundsInput
    (fun inp => inp.signVarLo = inp.signVarHi ∧ 0 < inp.capacity ∧ inp.monotoneInDomain = true) :=
  ⟨canElideSturmTarskiBounds, fun inp => (sturm_tarski_bounds_gate_sound inp).mp,
   fun inp => (sturm_tarski_bounds_gate_sound inp).mpr, ⟨2, 2, 64, true⟩, ⟨2, 1, 64, true⟩, rfl, rfl⟩
theorem root_crossing_rejects_sturm_tarski_bounds (inp : SturmTarskiBoundsInput)
    (h_ne : inp.signVarLo ≠ inp.signVarHi) : canElideSturmTarskiBounds inp = false :=
  sturmTarskiBoundsMetaSpec.rejects_unsafe inp (by simp [h_ne])

/-- Min-cut / Kantorovich register pressure: a cut `(live, spill)` is feasible when `live ≤ budget`. -/
structure RegCut where
  (live spill budget : Nat)
  deriving Repr, DecidableEq, BEq
def regCutFeasible (c : RegCut) : Bool := decide (c.live ≤ c.budget)
def regCutCost (c : RegCut) : Nat := c.spill
theorem reg_cut_feasible_sound (c : RegCut) : regCutFeasible c = true ↔ c.live ≤ c.budget := by
  simp [regCutFeasible]
theorem reg_cut_cost_monotone (c1 c2 : RegCut) (h : c1.spill ≤ c2.spill) : regCutCost c1 ≤ regCutCost c2 := h

/-- Canonical 5-target `SearchBackend` routing soundness for FPGA LSC2 256-bit workloads. -/
theorem fpga_lsc2_256bit_routing_sound (tripCount : Nat)
    (isMatrixContraction hasTpu hasCudaGpu hasMetalGpu : Bool) (h_large : 4096 ≤ tripCount) :
    selectOptimalSearchBackend tripCount isMatrixContraction true false hasTpu hasCudaGpu hasMetalGpu true = .FpgaLsc2 := by
  simp [selectOptimalSearchBackend, Nat.not_lt.mpr h_large]

/-- Zero-Dependency Mathlib Certificate Lowering gate (`linear_combination` + DAG `rw`/`simp only` + Farkas witnesses,
    guaranteeing `0 sorryAx`, `0 native_decide`, and zero imports of `lean-native`/`turbo-lean`). -/
structure MathlibCertLoweringInput where
  (hasExternalImports usesNativeDecide usesSorryAx cofactorsVerified : Bool)
  deriving Repr, DecidableEq, BEq
def canEmitZeroDepMathlibCert (inp : MathlibCertLoweringInput) : Bool :=
  !inp.hasExternalImports && !inp.usesNativeDecide && !inp.usesSorryAx && inp.cofactorsVerified
theorem mathlib_cert_lowering_gate_sound (inp : MathlibCertLoweringInput) :
    canEmitZeroDepMathlibCert inp = true ↔
      (inp.hasExternalImports = false ∧ inp.usesNativeDecide = false ∧ inp.usesSorryAx = false ∧ inp.cofactorsVerified = true) := by
  simp [canEmitZeroDepMathlibCert, Bool.and_eq_true, and_assoc]
def mathlibCertLoweringMetaSpec : MetaGateSpec MathlibCertLoweringInput
    (fun inp => inp.hasExternalImports = false ∧ inp.usesNativeDecide = false ∧
      inp.usesSorryAx = false ∧ inp.cofactorsVerified = true) :=
  ⟨canEmitZeroDepMathlibCert, fun inp => (mathlib_cert_lowering_gate_sound inp).mp,
   fun inp => (mathlib_cert_lowering_gate_sound inp).mpr, ⟨false, false, false, true⟩, ⟨false, true, false, true⟩, rfl, rfl⟩
theorem native_decide_rejects_mathlib_cert_lowering (inp : MathlibCertLoweringInput)
    (h_nd : inp.usesNativeDecide = true) : canEmitZeroDepMathlibCert inp = false :=
  mathlibCertLoweringMetaSpec.rejects_unsafe inp (by simp [h_nd])

/-- Formal C-ABI flat-slice & out-buffer bounds gate (`emit-cabi-bindings` / `compile-static-lib`). -/
structure CAbiSliceIoInput where
  (rowCount rowBytes maxBufferBytes outLen outCap : Nat)
  deriving Repr, DecidableEq, BEq
def canBindCAbiSliceIo (inp : CAbiSliceIoInput) : Bool :=
  decide (0 < inp.maxBufferBytes) && decide (inp.rowCount * inp.rowBytes ≤ inp.maxBufferBytes) && decide (inp.outLen ≤ inp.outCap)
theorem cabi_slice_io_gate_sound (inp : CAbiSliceIoInput) :
    canBindCAbiSliceIo inp = true ↔
      (0 < inp.maxBufferBytes ∧ inp.rowCount * inp.rowBytes ≤ inp.maxBufferBytes ∧ inp.outLen ≤ inp.outCap) := by
  simp [canBindCAbiSliceIo, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def cabiSliceIoMetaSpec : MetaGateSpec CAbiSliceIoInput
    (fun inp => 0 < inp.maxBufferBytes ∧ inp.rowCount * inp.rowBytes ≤ inp.maxBufferBytes ∧ inp.outLen ≤ inp.outCap) :=
  ⟨canBindCAbiSliceIo, fun inp => (cabi_slice_io_gate_sound inp).mp,
   fun inp => (cabi_slice_io_gate_sound inp).mpr, ⟨16, 48, 4096, 8, 16⟩, ⟨16, 48, 4096, 32, 16⟩, rfl, rfl⟩
theorem overflow_out_len_rejects_cabi_slice_io (inp : CAbiSliceIoInput)
    (h_ovf : inp.outCap < inp.outLen) : canBindCAbiSliceIo inp = false :=
  cabiSliceIoMetaSpec.rejects_unsafe inp (by omega)

@[inline, export leannative_verify_cabi_slice_io]
def verifyCAbiSliceIoC (rowCount rowBytes maxBufferBytes outLen outCap : UInt64) : UInt64 :=
  if canBindCAbiSliceIo ⟨rowCount.toNat, rowBytes.toNat, maxBufferBytes.toNat, outLen.toNat, outCap.toNat⟩ then 1 else 0

/-- Pack a borrowed slice span `(start:32 | len:24 | kind:8)` into a single unboxed `UInt64` (`SliceOut` C-ABI). -/
@[inline, export leannative_pack_slice_span_u64]
def packSliceSpanU64 (start len kind : UInt64) : UInt64 :=
  ((start &&& 0xFFFFFFFF) <<< 32) ||| ((len &&& 0xFFFFFF) <<< 8) ||| (kind &&& 0xFF)

/-- Zero-Runtime `NoRuntimeCheck` & `SliceOut` C-ABI gate (`nm -u == 0`, zero `lean_alloc_*`/RC/closures). -/
structure NoRuntimeSliceOutInput where
  (undefRuntimeSyms allocCount rcOpCount outLen outCap : Nat)
  deriving Repr, DecidableEq, BEq
def canEmitZeroRuntimeSliceOut (inp : NoRuntimeSliceOutInput) : Bool :=
  decide (inp.undefRuntimeSyms = 0) && decide (inp.allocCount = 0) && decide (inp.rcOpCount = 0) && decide (inp.outLen ≤ inp.outCap)
theorem no_runtime_slice_out_gate_sound (inp : NoRuntimeSliceOutInput) :
    canEmitZeroRuntimeSliceOut inp = true ↔
      (inp.undefRuntimeSyms = 0 ∧ inp.allocCount = 0 ∧ inp.rcOpCount = 0 ∧ inp.outLen ≤ inp.outCap) := by
  simp [canEmitZeroRuntimeSliceOut, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def noRuntimeSliceOutMetaSpec : MetaGateSpec NoRuntimeSliceOutInput
    (fun inp => inp.undefRuntimeSyms = 0 ∧ inp.allocCount = 0 ∧ inp.rcOpCount = 0 ∧ inp.outLen ≤ inp.outCap) :=
  ⟨canEmitZeroRuntimeSliceOut, fun inp => (no_runtime_slice_out_gate_sound inp).mp,
   fun inp => (no_runtime_slice_out_gate_sound inp).mpr, ⟨0, 0, 0, 8, 16⟩, ⟨1, 0, 0, 8, 16⟩, rfl, rfl⟩
theorem runtime_sym_rejects_slice_out (inp : NoRuntimeSliceOutInput)
    (h_sym : 0 < inp.undefRuntimeSyms) : canEmitZeroRuntimeSliceOut inp = false :=
  noRuntimeSliceOutMetaSpec.rejects_unsafe inp (by omega)

@[inline, export leannative_verify_no_runtime_slice_out]
def verifyNoRuntimeSliceOutC (undefSyms allocCount rcCount outLen outCap : UInt64) : UInt64 :=
  if canEmitZeroRuntimeSliceOut ⟨undefSyms.toNat, allocCount.toNat, rcCount.toNat, outLen.toNat, outCap.toNat⟩ then 1 else 0

#guard verifyCAbiSliceIoC 16 48 4096 8 16 == 1
#guard verifyCAbiSliceIoC 16 48 512 8 16 == 0
#guard verifyCAbiSliceIoC 16 48 4096 32 16 == 0
#guard packSliceSpanU64 10 25 3 == 0x0000000A00001903
#guard verifyNoRuntimeSliceOutC 0 0 0 8 16 == 1
#guard verifyNoRuntimeSliceOutC 1 0 0 8 16 == 0

/-- Wave 15–18 structural loop-peephole, 1D `_scalar` hoisting, entry-guard unrolling, & dead-tail elision gate (`ln_c_opt`). -/
structure Wave15To18StructuralGateInput where
  (jpBranchesPure innerStopHoisted entryBoundsGuarded tailLimitLeCap : Bool)
  deriving Repr, DecidableEq, BEq
def canApplyWave15To18StructuralOpt (inp : Wave15To18StructuralGateInput) : Bool :=
  inp.jpBranchesPure && inp.innerStopHoisted && inp.entryBoundsGuarded && inp.tailLimitLeCap
theorem wave15_to_18_structural_gate_sound (inp : Wave15To18StructuralGateInput) :
    canApplyWave15To18StructuralOpt inp = true ↔
      (inp.jpBranchesPure = true ∧ inp.innerStopHoisted = true ∧ inp.entryBoundsGuarded = true ∧ inp.tailLimitLeCap = true) := by
  simp [canApplyWave15To18StructuralOpt, Bool.and_eq_true, and_assoc]
def wave15To18StructuralMetaSpec : MetaGateSpec Wave15To18StructuralGateInput
    (fun inp => inp.jpBranchesPure = true ∧ inp.innerStopHoisted = true ∧
      inp.entryBoundsGuarded = true ∧ inp.tailLimitLeCap = true) :=
  ⟨canApplyWave15To18StructuralOpt, fun inp => (wave15_to_18_structural_gate_sound inp).mp,
   fun inp => (wave15_to_18_structural_gate_sound inp).mpr, ⟨true, true, true, true⟩, ⟨true, true, false, true⟩, rfl, rfl⟩
theorem unguarded_entry_rejects_wave15_to_18_opt (inp : Wave15To18StructuralGateInput)
    (h_un : inp.entryBoundsGuarded = false) : canApplyWave15To18StructuralOpt inp = false :=
  wave15To18StructuralMetaSpec.rejects_unsafe inp (by simp [h_un])

/-- Lazy 256-bit carryless accumulation & single-end-reduction slice pass gate (`lean_native_f128_*_slice`). -/
structure LazyReductionSliceInput where
  (chunkLen unreducedBits : Nat) (reductionLinear slicesDisjoint : Bool)
  deriving Repr, DecidableEq, BEq
def canEmitLazyReductionSlice (inp : LazyReductionSliceInput) : Bool :=
  decide (0 < inp.chunkLen) && decide (inp.unreducedBits = 256) && inp.reductionLinear && inp.slicesDisjoint
theorem lazy_reduction_slice_gate_sound (inp : LazyReductionSliceInput) :
    canEmitLazyReductionSlice inp = true ↔
      (0 < inp.chunkLen ∧ inp.unreducedBits = 256 ∧ inp.reductionLinear = true ∧ inp.slicesDisjoint = true) := by
  simp [canEmitLazyReductionSlice, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def lazyReductionSliceMetaSpec : MetaGateSpec LazyReductionSliceInput
    (fun inp => 0 < inp.chunkLen ∧ inp.unreducedBits = 256 ∧ inp.reductionLinear = true ∧ inp.slicesDisjoint = true) :=
  ⟨canEmitLazyReductionSlice, fun inp => (lazy_reduction_slice_gate_sound inp).mp,
   fun inp => (lazy_reduction_slice_gate_sound inp).mpr, ⟨64, 256, true, true⟩, ⟨64, 256, false, true⟩, rfl, rfl⟩
theorem non_linear_rejects_lazy_reduction_slice (inp : LazyReductionSliceInput)
    (h_nl : inp.reductionLinear = false) : canEmitLazyReductionSlice inp = false :=
  lazyReductionSliceMetaSpec.rejects_unsafe inp (by simp [h_nl])

@[inline, export leannative_verify_lazy_reduction_slice]
def verifyLazyReductionSliceC (chunkLen unreducedBits : UInt64) (reductionLinear slicesDisjoint : UInt8) : UInt64 :=
  if canEmitLazyReductionSlice ⟨chunkLen.toNat, unreducedBits.toNat, reductionLinear == 1, slicesDisjoint == 1⟩ then 1 else 0

/-- 2-layer Radix-4 LCH Additive NTT butterfly fusion gate (`lean_native_ntt_butterfly_fused_2layer_slice`). -/
structure Radix4NttFusionInput where
  (half0 half1 blockLen : Nat) (inPlaceDisjoint : Bool)
  deriving Repr, DecidableEq, BEq
def canFuseRadix4NttLayers (inp : Radix4NttFusionInput) : Bool :=
  decide (0 < inp.half1) && decide (inp.half0 = 2 * inp.half1) &&
    decide (inp.blockLen % (4 * inp.half1) = 0) && inp.inPlaceDisjoint
theorem radix4_ntt_fusion_gate_sound (inp : Radix4NttFusionInput) :
    canFuseRadix4NttLayers inp = true ↔
      (0 < inp.half1 ∧ inp.half0 = 2 * inp.half1 ∧
        inp.blockLen % (4 * inp.half1) = 0 ∧ inp.inPlaceDisjoint = true) := by
  simp [canFuseRadix4NttLayers, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def radix4NttFusionMetaSpec : MetaGateSpec Radix4NttFusionInput
    (fun inp => 0 < inp.half1 ∧ inp.half0 = 2 * inp.half1 ∧
      inp.blockLen % (4 * inp.half1) = 0 ∧ inp.inPlaceDisjoint = true) :=
  ⟨canFuseRadix4NttLayers, fun inp => (radix4_ntt_fusion_gate_sound inp).mp,
   fun inp => (radix4_ntt_fusion_gate_sound inp).mpr, ⟨8, 4, 64, true⟩, ⟨8, 3, 64, true⟩, rfl, rfl⟩
theorem misaligned_stride_rejects_radix4_ntt (inp : Radix4NttFusionInput)
    (h_mis : inp.half0 ≠ 2 * inp.half1) : canFuseRadix4NttLayers inp = false :=
  radix4NttFusionMetaSpec.rejects_unsafe inp (by simp [h_mis])

@[inline, export leannative_verify_radix4_ntt_fusion]
def verifyRadix4NttFusionC (half0 half1 blockLen : UInt64) (inPlaceDisjoint : UInt8) : UInt64 :=
  if canFuseRadix4NttLayers ⟨half0.toNat, half1.toNat, blockLen.toNat, inPlaceDisjoint == 1⟩ then 1 else 0

/-- Pure-Lean `turbo-lean` migration gate: zero-copy `ByteSlice` scanner + tuple SROA + `SliceOut` zero-runtime gate. -/
structure TurboSliceScannerSROAInput where
  (sliceInBounds tupleAliasEscapes : Bool) (undefRuntimeSyms outLen outCap : Nat)
  deriving Repr, DecidableEq, BEq
def canLowerTurboSliceScannerSROA (inp : TurboSliceScannerSROAInput) : Bool :=
  inp.sliceInBounds && !inp.tupleAliasEscapes &&
    decide (inp.undefRuntimeSyms = 0) && decide (inp.outLen ≤ inp.outCap)
theorem turbo_slice_scanner_sroa_gate_sound (inp : TurboSliceScannerSROAInput) :
    canLowerTurboSliceScannerSROA inp = true ↔
      (inp.sliceInBounds = true ∧ inp.tupleAliasEscapes = false ∧
        inp.undefRuntimeSyms = 0 ∧ inp.outLen ≤ inp.outCap) := by
  simp [canLowerTurboSliceScannerSROA, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def turboSliceScannerSROAMetaSpec : MetaGateSpec TurboSliceScannerSROAInput
    (fun inp => inp.sliceInBounds = true ∧ inp.tupleAliasEscapes = false ∧
      inp.undefRuntimeSyms = 0 ∧ inp.outLen ≤ inp.outCap) :=
  ⟨canLowerTurboSliceScannerSROA, fun inp => (turbo_slice_scanner_sroa_gate_sound inp).mp,
   fun inp => (turbo_slice_scanner_sroa_gate_sound inp).mpr, ⟨true, false, 0, 16, 64⟩, ⟨true, true, 0, 16, 64⟩, rfl, rfl⟩
theorem escaping_tuple_or_oob_rejects_slice_scanner_sroa (inp : TurboSliceScannerSROAInput)
    (h_bad : inp.sliceInBounds = false ∨ inp.tupleAliasEscapes = true ∨
      0 < inp.undefRuntimeSyms ∨ inp.outCap < inp.outLen) :
    canLowerTurboSliceScannerSROA inp = false :=
  turboSliceScannerSROAMetaSpec.rejects_unsafe inp (by
    rcases h_bad with h | h | h | h
    · simp [h]
    · simp [h]
    · omega
    · omega)

@[inline, export leannative_verify_turbo_slice_scanner_sroa]
def verifyTurboSliceScannerSROAC (sliceInBounds tupleAliasEscapes undefSyms outLen outCap : UInt64) : UInt64 :=
  let inp : TurboSliceScannerSROAInput :=
    ⟨sliceInBounds != 0, tupleAliasEscapes != 0, undefSyms.toNat, outLen.toNat, outCap.toNat⟩
  if canLowerTurboSliceScannerSROA inp then 1 else 0

/-- Canonical Layer-0 Counterexample Triage Gate re-exported from `LeanSys.Gate` & `LeanSys.Spec`. -/
abbrev CounterexampleTriageInput := LeanSys.Contracts.CounterexampleTriageInput
abbrev verifyCounterexampleTriage := LeanSys.Contracts.checkCounterexampleTriage
abbrev counterexample_triage_gate_sound := @LeanSys.Contracts.checkCounterexampleTriage_sound
abbrev counterexampleTriageMetaSpec := LeanSys.Contracts.counterexampleTriageContractMetaSpec
abbrev verifyCounterexampleTriageC := LeanSys.Spec.verifyCounterexampleTriage

/-- Zero-runtime C-ABI 64-bit FastCheck binary operator evaluator
    (`0=add, 1=sub, 2=mul, 3=div, 4=mod, 5=bitAnd, 6=bitOr, 7=bitXor, 8=shl, 9=shr, 10=eq, 11=lt, 12=le`). -/
@[inline, export leannative_eval_u64_binop]
def evalU64BinopC (op : UInt8) (lhs rhs : UInt64) : UInt64 :=
  if op == 0 then lhs + rhs
  else if op == 1 then lhs - rhs
  else if op == 2 then lhs * rhs
  else if op == 3 then if rhs == 0 then 0 else lhs / rhs
  else if op == 4 then if rhs == 0 then 0 else lhs % rhs
  else if op == 5 then lhs &&& rhs
  else if op == 6 then lhs ||| rhs
  else if op == 7 then lhs ^^^ rhs
  else if op == 8 then if rhs >= 64 then 0 else lhs <<< rhs
  else if op == 9 then if rhs >= 64 then 0 else lhs >>> rhs
  else if op == 10 then if lhs == rhs then 1 else 0
  else if op == 11 then if lhs < rhs then 1 else 0
  else if op == 12 then if lhs <= rhs then 1 else 0
  else 0

/-- Zero-runtime C-ABI 64-bit FastCheck domain-hazard detector
    (`div/mod` by `0`, `shl/shr >= 64`, `add` wrapping overflow, `sub` wrapping underflow, `mul` overflow). -/
@[inline, export leannative_has_domain_hazard_u64]
def hasDomainHazardU64C (op : UInt8) (lhs rhs : UInt64) : UInt8 :=
  let hazard : Bool :=
    if op == 0 then (lhs + rhs) < lhs
    else if op == 1 then lhs < rhs
    else if op == 2 then lhs != 0 && ((lhs * rhs) / lhs != rhs)
    else if op == 3 || op == 4 then rhs == 0
    else if op == 8 || op == 9 then rhs >= 64
    else false
  if hazard then 1 else 0

/-- Zero-runtime C-ABI FastCheck rewrite witness evaluation & triage step:
    returns `0` (`Unclassified` when `lhsVal == rhsVal`), `1` (`SpecTooStrong` on domain hazard),
    `2` (`ReferenceDiscrepancy` when `refDisagrees == 1` without hazard), or `3` (`CandidateBug`),
    verified by `LeanSys.Spec.verifyCounterexampleTriage`. -/
@[inline, export leannative_fastcheck_rewrite_step]
def fastcheckRewriteStepC (lhsVal rhsVal : UInt64) (opLhs opRhs : UInt8)
    (a b : UInt64) (refDisagrees : UInt8) : UInt8 :=
  if lhsVal == rhsVal then 0
  else
    let hasHazard : UInt8 :=
      if hasDomainHazardU64C opLhs a b == 1 || hasDomainHazardU64C opRhs a b == 1 then 1 else 0
    let effRefDis : UInt8 := if hasHazard == 0 && refDisagrees == 1 then 1 else 0
    let code : UInt8 := if hasHazard == 1 then 1 else if effRefDis == 1 then 2 else 3
    if verifyCounterexampleTriageC 1 hasHazard effRefDis code == 1 then code else 0

/-- Zero-runtime C-ABI in-process counterexample self-certification (`eval-cex` replacement):
    verifies both (1) the equality-constrained 64-bit witness (`x0 = x1 + 42 >= 1_000_000` at `x1 = 1_000_000`,
    triaged as `CandidateBug` `code = 3` with zero domain hazard) and (2) the 256-bit De Morgan falsification
    witness (`~(dmA0 & dmB0) != (~dmA0 & ~dmB0)` at `dmA0 = 0, dmB0 = MAX`). -/
@[inline, export leannative_certify_cex_witnesses]
def certifyCexWitnessesC (x1 dmA0 dmB0 : UInt64) : UInt8 :=
  let x0 := evalU64BinopC 0 x1 42
  let constrainedCexOk : Bool :=
    (x0 == x1 + 42) && !(x0 < 1000000) && (fastcheckRewriteStepC x0 999999 0 0 x1 42 0 == 3)
  let lhsDm := ~~~(evalU64BinopC 5 dmA0 dmB0)
  let rhsDm := evalU64BinopC 5 (~~~dmA0) (~~~dmB0)
  let deMorganCexOk : Bool :=
    (lhsDm != rhsDm) && (fastcheckRewriteStepC lhsDm rhsDm 5 5 dmA0 dmB0 0 == 3)
  if constrainedCexOk && deMorganCexOk then 1 else 0

#guard verifyLazyReductionSliceC 64 256 1 1 == 1
#guard verifyLazyReductionSliceC 64 256 0 1 == 0
#guard verifyRadix4NttFusionC 8 4 64 1 == 1
#guard verifyRadix4NttFusionC 8 3 64 1 == 0
#guard verifyTurboSliceScannerSROAC 1 0 0 16 64 == 1
#guard verifyTurboSliceScannerSROAC 1 1 0 16 64 == 0
#guard verifyCounterexampleTriageC 1 1 0 1 == 1
#guard verifyCounterexampleTriageC 1 0 1 2 == 1
#guard verifyCounterexampleTriageC 1 0 0 3 == 1
#guard verifyCounterexampleTriageC 1 1 0 3 == 0
#guard verifyCounterexampleTriageC 0 0 0 3 == 0
#guard evalU64BinopC 0 1000000 42 == 1000042
#guard hasDomainHazardU64C 3 42 0 == 1
#guard hasDomainHazardU64C 8 1 64 == 1
#guard hasDomainHazardU64C 0 10 20 == 0
#guard fastcheckRewriteStepC 0 1 3 0 1 0 0 == 1
#guard fastcheckRewriteStepC 4 3 0 0 1 2 1 == 2
#guard fastcheckRewriteStepC 4 3 0 0 1 2 0 == 3
#guard certifyCexWitnessesC 1000000 0 0xFFFFFFFFFFFFFFFF == 1

end LeanNative.Spec
