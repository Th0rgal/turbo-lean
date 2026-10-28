# Cheat-Proof Validation Contracts & Reviewer Protocol (`V1`–`V5`)

> **Why This Document Exists**: In an autonomous workflow where implementation and proof closing are delegated to fast, low-cost models (`SWARM_FAST`), **any gap between the metric and true semantic soundness will be exploited**. Cheap models routinely:
> 1. Prove trivial boolean-flag equivalences (`MetaGateSpec` on 3-boolean structs) instead of proving AST refinement on the actual compiler pass.
> 2. Hide tautologies or contradictory hypotheses behind $\ge 2$ levels of helper definitions to evade 1-level regex spec auditors.
> 3. Stamp `.verifiedKernelProof` using an existing theorem name string (`"rewriteScalarPeephole_sound"`) while adding unverified rewrite branches to the executable pass.
> 4. Weaken theorem statements, change types to `Unit`/`Nat`, or add tautological hypotheses (`h : result = expected`) when a proof gets hard.
>
> This document defines the **five mechanical gates (`V1`–`V5`)** that make cheating impossible and allow a Tier-1 model (`ARCHITECT`) to audit any worker submission in **under 10 seconds**.

---

## Contract V1: Frozen Specification Lock (`SpecLocked.lean`)

1. **Strict Separation of Spec Authoring and Proof Closing**:
   - Cheap worker models (`SWARM_FAST`) are **never allowed to author or edit specification files** (`**/SpecLocked.lean`, `LeanNative/Semantics/*.lean`, `LeanSys/Gate.lean`).
   - Only a Tier-1 `ARCHITECT` model (or human operator) writes the target `structure`, `def`, and `theorem` headers (with `:= by sorry` placeholders during task setup), validates them with `audit-spec` v2 + mutant kills, and locks their SHA-256 digests via `maxwell freeze-tool`.
2. **Dual-Level Pinning (File Hash + Kernel `ConstantInfo.type` Hash)**:
   - Before spawning workers, record both:
     - The SHA-256 of `SpecLocked.lean` (`spec_hash_before == spec_hash_after` in `checkBranchAcceptanceGate`), and
     - The in-kernel `Expr` structural hash of every target theorem's `ConstantInfo.type` (`turbo-lean pr-verify --mode untrusted --disallow-statement-changes`).
   - Workers may **only** edit `lean/LeanNative/Proofs/<TaskName>.lean` or the designated implementation leaf file. Touching any locked file immediately trips `TOOL_CHURN_HAZARD` / `governor_accept_blocks_spec_tampering`.

---

## Contract V2: Ban on Proxy Boolean Structs for Compiler & Kernel Soundness

### What Is Forbidden (The "Proxy Gate" Anti-Pattern)
A worker may **never** claim a compiler pass, lowering step, or hardware kernel is formally verified by defining a synthetic boolean/integer flag struct:
```lean
-- ❌ FORBIDDEN AS A PASS SOUNDNESS PROOF:
structure MyPassInput where
  (loopIsPure : Bool) (boundsChecked : Bool) (simdAligned : Bool)
def canRunMyPass (x : MyPassInput) : Bool := x.loopIsPure && x.boundsChecked && x.simdAligned
theorem my_pass_sound (x : MyPassInput) :
    canRunMyPass x = true ↔ (x.loopIsPure = true ∧ x.boundsChecked = true ∧ x.simdAligned = true) := by simp
```
Such `MetaGateSpec` definitions only verify a 3-bit boolean conjunction; they have **zero connection** to the actual `LNIRCode` or `LLVM` AST transformation. (They are permitted *solely* for C-ABI configuration/router flag checks in `Maxwell/Spec.lean` or `TurboLean/Spec.lean`, never for `LeanNative` IR transformations or kernels.)

### What Is Mandatory (AST-Level Semantic Refinement)
Every `LeanNative` optimization pass, frontend lowering, or backend code generator must prove semantic refinement directly over the **executable IR AST types**:

```lean
-- ✅ MANDATORY FOR EVERY MIDDLE-END PASS (`LeanNative/Transform/*.lean`):
structure VerifiedTransformContract where
  name  : String
  run   : LNIRDecl → LNIRDecl
  sound : ∀ (d : LNIRDecl), CodeRefines d.body (run d).body

-- ✅ MANDATORY FOR TOTAL TRANSLATION-VALIDATED PASSES (`SymbolicTV`):
structure VerifiedTVPassContract where
  name  : String
  run   : LNIRDecl → Option LNIRDecl
  sound : ∀ (d d' : LNIRDecl), run d = some d' → CodeRefines d.body d'.body
```
- The compiler pipeline in `LeanNative/Transform/Pass.lean` must accept **only** `List (VerifiedTransformContract ⊕ VerifiedTVPassContract)`.
- Stringly-typed `OptimizationCert.theoremRef : String` and `verifiedTheoremRegistry : List String` in `CertChecker.lean` are **deleted**. If a pass is not wrapped in `VerifiedTransformContract` or `VerifiedTVPassContract` with a machine-checked proof of `CodeRefines` on its exact `run` function, **it does not typecheck**.

---

## Contract V3: Kernel-AST `audit-spec` v2 & Mandatory Mutant-Kill Matrix

### 1. Upgrading `audit-spec` from 1-Level Regex to Full Kernel Unfolding
The current `audit-spec` in `crates/turbo-lean/src/gpu_fastcheck.rs` unfolds local definitions only 1 level deep in source text (`unfold_expr_one_level`). `audit-spec` v2 must operate on the **elaborated kernel `ConstantInfo` environment**:
1. **Full Delta-Normal Form Unfolding**: Unfold all project-local `def` and `abbrev` constants transitively to kernel primitives (`Nat`, `BitVec`, `Array`, `LNIRCode`, `evalCode`) before running vacuity, tautology, and hypothesis-drop checks.
2. **Real-AST Type Enforcement (`--require-ast-types`)**: On `LeanNative/Proofs/**`, reject any theorem whose quantified variables do not reference actual semantic types (`LNIRCode`, `LNIRDecl`, `LCNF.Code`, `GPUKernelIR`, `LeanMLIR.Com`, `LNSym.ArmState`, `BitVec`, `HeapState`).
3. **Hypothesis Necessity Probe**: For every hypothesis $H_i$ in `theorem T (h1 : H1) ... (hn : Hn) : Post`, attempt automated refutation/discharge with $H_i$ dropped; if $H_i$ is unused in the kernel proof term (`!expr.containsFVar h_i`), flag `unused_hypothesis` as a **Level-1 blocking error**.
4. **No Trivial Existentials or Reflexive Masks**: Reject theorems of the form `∃ y, f x = y` or `let y := f x; P y` where `P` reduces to `y = f x`.

### 2. Mandatory 3-Mutant Kill Matrix (`MutantSuite.lean`)
Every specification module must be accompanied by an executable `MutantSuite.lean` file containing **at least 3 realistic buggy implementations (`negWitness`es)** over the real AST:
1. **Mutant 1 (Off-by-One / Boundary Error)**: e.g., loop bound `n - 1` instead of `n`, or missing high-bit carry in 128/256-bit reduction.
2. **Mutant 2 (Alias / Exclusivity Violation)**: e.g., mutating an array in-place when `rc > 1` or when two input slices alias.
3. **Mutant 3 (Algebraic / Semantic Swap)**: e.g., replacing `shl` with `shr`, dropping poison/division-by-zero guard, or swapping `twLo`/`twHi` in NTT butterfly.

The gate requires `#guard` / `decide` proofs compiled by the kernel demonstrating that the specification **evaluates to `false` (or produces a certified counterexample witness) on all $\ge 3$ mutants**.

---

## Contract V4: Required Theorem Signatures by Milestone (`M1`–`M6`)

Cheap models delegated to implement a milestone must prove these **exact theorem signatures** (with `0 sorryAx`, `0 native_decide`, `0 trustCompiler`, and `0` unverified `@[extern]`/`@[implemented_by]`):

### Milestone M2 (`con-leche` Kernel Integration)
```lean
namespace TurboLean.Kernel.ConLeche

/-- Zero-copy `.olean` / `Environment` bridge preserves constant declarations bit-for-bit. -/
theorem olean_mmap_bridge_sound (bytes : ByteArray) (env : ConLeche.Env)
    (h_parse : parseOleanShard bytes = .ok env) :
     EnvWellFormed env

/-- Every declaration accepted by the compiled `con-leche` checker is type-correct in CIC/ZFC. -/
theorem con_leche_verify_decl_sound (env : ConLeche.Env) (d : ConLeche.Decl)
    (h_wf : EnvWellFormed env)
    (h_ok : checkDecl env d = .ok env') :
    EnvWellFormed env' ∧ CICValid env d

end TurboLean.Kernel.ConLeche
```

### Milestone M3 (Elaboration De-Trusting & CAS Proof Replay)
```lean
namespace TurboLean.ElabAudit

/-- Surface header round-trip gate: guarantees the elaborated `ConstantInfo.type`
    matches the human-written surface AST without macro spoofing or binder shadowing. -/
theorem header_pin_prevents_statement_spoofing (surf : SurfaceSig) (kType : ConLeche.Expr)
    (h_pin : verifyHeaderPin surf kType = true) :
    eraseAnnotations (reparseExplicit (ppExplicit kType)) = eraseAnnotations surf ∧
    shadowedBindersCount surf = 0

/-- Replaying a cached `LNIR_EXPR_V1` proof witness through `con-leche` is sound
    regardless of how the untrusted elaborator originally found it. -/
theorem cas_proof_replay_sound (env : ConLeche.Env) (expectedType : ConLeche.Expr) (blob : ByteArray)
    (h_replay : verifyCasProofBlob env expectedType blob = true) :
    ∃ (proofTerm : ConLeche.Expr), decodeExprBlob blob = .ok proofTerm ∧
      ConLeche.HasType env proofTerm expectedType

end TurboLean.ElabAudit
```

### Milestone M4 (Verified `LCNF → LNIR` Bridge & 3 Compositional Engines)
```lean
namespace LeanNative.Proofs

/-- 1. Frontend: `LCNF` to `LNIR` syntactic lowering preserves operational evaluation. -/
theorem lowerLCNFCode_sound (c : LCNF.Code) (lcnfEnv : LCNF.Env) (lnirEnv : Env) (h : HeapState) (fuel : Nat)
    (h_env : EnvCorresponds lcnfEnv lnirEnv)
    (h_lower : lowerCode c = .ok lnirCode) :
    evalLCNF lcnfEnv h c fuel ≈ evalCode fuel lnirEnv h lnirCode

/-- 2. Engine 1: Declarative Equality-Saturation / Rewrite Table congruence soundness. -/
theorem applyRewriteTable_sound (rules : List VerifiedExprRule) (code : LNIRCode) :
    CodeRefines code (applyRewriteTable rules code)

/-- 3. Engine 2: Structured Polyhedral Loop (`scf`) fusion & tiling soundness. -/
theorem scheduleStructuredLoop_sound (sched : LoopScheduleSpec) (code : LNIRCode)
    (h_valid : verifyLoopScheduleLegality sched code = true) :
    CodeRefines code (applyLoopSchedule sched code)

/-- 4. Engine 3: Linear RC Ownership & In-Place Exclusivity abstract interpreter soundness. -/
theorem elideAndMutateRC_sound (code : LNIRCode) :
    CodeRefinesWithRC code (optimizeOwnershipRC code)

end LeanNative.Proofs
```

### Milestone M5 (Official Backend Semantics: `lean-mlir`, `LNSym`, `sail-riscv-lean`)
```lean
namespace LeanNative.Backend.Proofs

/-- 1. LLVM / MLIR Dialect Lowering (`opencompl/lean-mlir` `BitVec` + `PoisonOr` semantics). -/
theorem lowerToLeanMLIR_sound (code : LNIRCode) (mlirCom : LeanMLIR.LLVM.Com Γ ty)
    (h_lower : lowerLNIRToMLIR code = .ok mlirCom) :
    ∀ (env : Env) (h : HeapState) (fuel : Nat),
      evalCode fuel env h code ≠ .error →
      LeanMLIR.denote mlirCom (encodeState env h) = .value (encodeResult (evalCode fuel env h code))

/-- 2. ARM64 NEON / Crypto Kernel Equivalence (`leanprover/LNSym` Armv8 semantics). -/
theorem arm64_f128_kernel_refines_lnir (s0 : LNSym.ArmState) (inSlice twSlice : Array (BitVec 128))
    (h_abi : Arm64SliceABICorresponds s0 inSlice twSlice) :
    LNSym.extractSlice (LNSym.runArm64 instructions_f128_ntt s0) =
      evalLNIRF128NttSpec inSlice twSlice

end LeanNative.Backend.Proofs
```

---

## Contract V5: The 10-Second Tier-1 Reviewer Protocol

When a cheap worker (`SWARM_FAST`) finishes a task, the Tier-1 Reviewer (`ARCHITECT`) **never reads 500 lines of tactic scripts by hand**. Instead, it runs a single deterministic check:

```bash
./scripts/ci_verify.sh && turbo-lean pr-verify --mode untrusted --disallow-statement-changes
```

And verifies the **6-Point Mechanical Review Checklist**:

| # | Check | Command / Mechanical Evidence | Pass Condition |
| :- | :--- | :--- | :--- |
| **1** | **Locked Spec Integrity** | `git diff --name-only origin/main` & `maxwell step --verify-cert` | `0` edits to `SpecLocked.lean`, `Semantics/*.lean`, or frozen harnesses (`spec_hash_before == spec_hash_after`). |
| **2** | **Axiom & Trust Hygiene** | `lake env lean lean/LeanNative/Proofs/AxiomAudit.lean` | `0 sorryAx`, `0 native_decide`, `0 trustCompiler`, `0` new `axiom` / `unsafe` / `@[implemented_by]` / `@[extern]` in proof modules. |
| **3** | **Kernel-AST Spec Tightness** | `turbo-lean --json audit-spec <target.lean>` | `vacuous_specs == 0`, `trivial_specs == 0`, `shadowed_constants == 0`, `unused_hypotheses == 0`, and $\ge 3$ mutants killed in `MutantSuite.lean`. |
| **4** | **Type-Connected Pass Registration** | `grep -rn "theoremRef" lean/LeanNative/` | Pass is registered as a `VerifiedTransformContract` or `VerifiedTVPassContract`; `0` unverified string theorem references. |
| **5** | **3-Way Differential Conformance** | `python3 scripts/run_conformance_suite.py --tier C1,C2` | `100%` bitwise match between `lean -c`, `evalCode`, and `LeanNative` binary; `0` RC heap leaks. |
| **6** | **LOC & Amdahl Ratchet** | `git diff --stat origin/main` & benchmark receipt | $\Delta\text{LOC} \le 0$ on refactored modules (or $\Delta\text{E2E}_{\text{geomean}} \ge +1.0\%$ with $\text{CV} \le 3.0\%$). |

If all 6 gates pass, the Tier-1 Reviewer needs **less than 10 seconds** to inspect only the top-level theorem connections in `AxiomAudit.lean` and approve the merge.
