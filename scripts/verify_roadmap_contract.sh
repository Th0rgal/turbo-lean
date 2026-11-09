#!/usr/bin/env bash
# Local Mechanical Reviewer Checklist (Contract V5 in roadmap/VALIDATION_CONTRACTS.md)
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TOOLCHAIN="$(tr -d '[:space:]' < "$ROOT_DIR/lean/lean-toolchain")"
TOOLCHAIN_DIR="leanprover--lean4---${TOOLCHAIN#leanprover/lean4:}"
for cand in \
  "$ROOT_DIR/target/release" \
  "$ROOT_DIR/target/debug" \
  "${ELAN_HOME:-$HOME/.elan}/toolchains/$TOOLCHAIN_DIR/bin" \
  "${ELAN_HOME:-$HOME/.elan}/bin" \
  "${CARGO_HOME:-$HOME/.cargo}/bin" \
  "$HOME/.local/bin"; do
  if [ -d "$cand" ]; then
    PATH="$cand:$PATH"
  fi
done
export PATH

if [ -n "${TURBO_AUDITOR_BIN+x}" ]; then
  TURBO_BIN="$TURBO_AUDITOR_BIN"
  if [ -z "$TURBO_BIN" ] || [ ! -x "$TURBO_BIN" ]; then
    echo "[FAIL] TURBO_AUDITOR_BIN=${TURBO_BIN:-<empty>} is missing or not executable" >&2
    exit 1
  fi
else
  TURBO_BIN="$ROOT_DIR/target/release/turbo-lean"
  if [ ! -x "$TURBO_BIN" ]; then
    TURBO_BIN="$(command -v turbo-lean || true)"
  fi
fi
FULL_BIN="$ROOT_DIR/lean/.lake/build/bin/lean-native"
CORE_BIN="$ROOT_DIR/lean/.lake/build/bin/lean-native-core"
ZYGOTE_BIN="$ROOT_DIR/lean/.lake/build/bin/turbo-zygote"

if [ -z "$TURBO_BIN" ] || [ ! -x "$TURBO_BIN" ]; then
  echo "[FAIL] turbo-lean binary not found or not executable" >&2
  exit 1
fi
if [ ! -x "$FULL_BIN" ]; then
  echo "[FAIL] $FULL_BIN not found; build with (cd lean && lake build lean-native)" >&2
  exit 1
fi
if [ ! -x "$CORE_BIN" ]; then
  echo "[FAIL] $CORE_BIN not found; build with (cd lean && lake build lean-native-core)" >&2
  exit 1
fi
if [ ! -x "$ZYGOTE_BIN" ]; then
  echo "[FAIL] $ZYGOTE_BIN not found; build with (cd lean && lake build turbo-zygote)" >&2
  exit 1
fi

echo "=== [1/9] Spec & Documentation Pinning Ratchet (Contract V1) ==="
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check

echo "=== [2/9] Multi-Hop Vacuity, Tightness & Packing Audit (audit-spec v2) ==="
"$TURBO_BIN" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert d['tight_specs'] == d['total_specs_audited'] and d['tight_specs'] == 98, d
assert len(d.get('droppable_hypotheses', [])) == 0, d
assert len(d.get('horizontal_packing_warnings', [])) == 0, d
print(f'  [OK] TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 droppable, 0 packing warnings)')
"
"$TURBO_BIN" --json audit-spec lean/LeanNative/Spec.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert d['tight_specs'] == d['total_specs_audited'] and d['tight_specs'] == 124, d
assert len(d.get('droppable_hypotheses', [])) == 0, d
print(f'  [OK] LeanNative/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 droppable)')
"
"$TURBO_BIN" --json audit-spec lean/LeanNative/Proofs/MutantSuite.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert d['tight_specs'] == d['total_specs_audited'] and d['tight_specs'] >= 4, d
assert len(d.get('droppable_hypotheses', [])) == 0, d
print(f'  [OK] MutantSuite.lean (M6): {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 droppable)')
"

echo "=== [2b/9] Configurable Anti-Reward-Hacking & Shadow-Namespace Gate (audit-spec v2.1, Contract V1/V2/V3) ==="
"$TURBO_BIN" --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/ lean/LeanNative/Transform/ lean/TurboLean/ConLeche.lean lean/TurboLean/ElabAudit.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert len(d.get('forbidden_scope_decls', [])) == 0, d
assert len(d.get('stub_defs', [])) == 0, d
print(f'  [OK] audit-spec v2.1 (strict-proofs) on M2-M5 proof & transform modules: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 stub_defs, 0 forbidden_scope_decls)')
"

echo "=== [3/9] In-Kernel Transitive Axiom Gate (Lean.collectAxioms) ==="
"$CORE_BIN" audit-axioms --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['passed'] is True, d
assert d['theoremsAudited'] >= 235, d
assert d['forbiddenAxiomsFound'] == [], d
names = {r['theoremName'] for r in d['results']}
required = [
    'LeanNative.Proofs.applyExprRules_sound',
    'LeanNative.Proofs.applyRewriteTable_sound',
    'LeanNative.Proofs.lowerRealLCNFCode_sound',
    'LeanNative.Proofs.lowerRealLCNFDecl_sound',
    'LeanNative.Transform.optimizeEqSatCode_sound',
    'LeanNative.Transform.scheduleStructuredLoop_sound',
    'LeanNative.Transform.elideAndMutateRC_sound',
    'LeanNative.Backend.Proofs.lowerToLeanMLIR_sound',
    'LeanNative.Backend.Proofs.arm64_f128_kernel_refines_lnir',
    'ConLeche.inferType_sound',
    'ConLeche.con_leche_verify_decl_sound',
    'ConLeche.olean_mmap_bridge_sound',
    'TurboLean.ElabAudit.header_pin_prevents_statement_spoofing',
    'TurboLean.ElabAudit.cas_proof_replay_sound',
    'LeanNative.Proofs.mutant1_off_by_one_killed',
    'LeanNative.Proofs.mutant2_exclusivity_violation_killed',
    'LeanNative.Proofs.mutant3_algebraic_swap_killed',
    'LeanNative.Proofs.all_three_mandatory_mutants_killed',
    'LeanNative.Proofs.llvm_sdiv64_min_neg1_ub',
    'LeanNative.Proofs.llvm_null_load_ub',
    'LeanNative.Proofs.llvm_null_store_ub',
    'LeanNative.Proofs.llvm_oob_gep_inbounds_load_ub',
    'LeanNative.Proofs.stablehlo_sdiv64_min_neg1_eq',
    'LeanNative.Proofs.stablehlo_srem64_min_neg1_zero',
    'LeanNative.Proofs.stablehlo_sdiv_zero_traps',
    'LeanNative.Proofs.stablehlo_clampStart_bounds',
    'LeanNative.Proofs.msl_shift_out_of_range_traps',
    'LeanNative.Proofs.ptx_rem_zero_traps',
]
missing = [r for r in required if r not in names]
assert not missing, f'Missing mandatory theorems in AxiomAudit: {missing}'
print(f'  [OK] AxiomAudit: {d[\"theoremsAudited\"]} theorems verified in kernel (0 sorryAx, 0 trustCompiler)')
"

echo "=== [4/9] Verified Pass Contract & Bridge/CoreCLI Hygiene Gate (Contract V2, M4 & M5) ==="
grep -q "structure VerifiedCodePassContract" lean/LeanNative/Transform/Pass.lean
grep -q "def verifiedAlgebraicPeepholeContract : VerifiedCodePassContract" lean/LeanNative/Transform/AlgebraicOpt.lean
grep -q "def verifiedEqSatContract.*: VerifiedCodePassContract" lean/LeanNative/Transform/EqSat.lean
grep -q "def verifiedLoopScheduleContract.*: VerifiedCodePassContract" lean/LeanNative/Transform/LoopSchedule.lean
grep -q "def verifiedOwnershipRCContract : VerifiedCodePassContract" lean/LeanNative/Transform/OwnershipRC.lean
grep -q "def canonicalScalarBinOpTable" lean/LeanNative/IR/Bridge.lean
test "$(grep -c '\.endsWith' lean/LeanNative/IR/Bridge.lean || true)" -eq 0
test "$(wc -l < lean/LeanNative/IR/Bridge.lean)" -le 350
test "$(wc -l < lean/LeanNative/Driver/CoreCLI.lean)" -le 1000
test ! -f lean/LeanNative/Driver/KernelTemplates.lean
echo "  [OK] Bridge.lean ($(wc -l < lean/LeanNative/IR/Bridge.lean) LOC <= 350) & CoreCLI.lean ($(wc -l < lean/LeanNative/Driver/CoreCLI.lean) LOC <= 1000) pass all hygiene & LOC gates"
"$CORE_BIN" verify-certs --canonical-benchmark --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['verified'] is True and d['overallAssurance'] in ('Tested', 'TranslationValidated'), d
assert any(r['declName'] == 'sarray_scale_bias' and r['overallAssurance'] == 'TranslationValidated' for r in d['declSummaries']), d
print(f'  [OK] Default Hybrid/TV Pass Certificates: verified={d[\"verified\"]}, assurance={d[\"overallAssurance\"]}, decls={len(d[\"declSummaries\"])}')
"
"$CORE_BIN" verify-certs --canonical-benchmark --verified-kernel-only --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['verified'] is True and d['overallAssurance'] == 'VerifiedKernelProof', d
print(f'  [OK] Kernel-Proved Pass Certificates (--verified-kernel-only): verified={d[\"verified\"]}, assurance={d[\"overallAssurance\"]}, decls={len(d[\"declSummaries\"])}')
"

echo "=== [5/9] Segregated Plugin & Adversarial Mutant Gate (Law 1) ==="
"$CORE_BIN" plugins --canonical-benchmark --test-adversarial --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['adversarialRejected'] is True and d['rejectedCount'] >= 1, d
assert all(a['tvVerified'] for a in d['declAudits']), d
print(f'  [OK] Segregated Plugins: accepted={d[\"acceptedCount\"]}, rejected={d[\"rejectedCount\"]}, adversarialRejected={d[\"adversarialRejected\"]}')
"

echo "=== [6/9] 3-Way Differential Conformance Suite, Grammar-Guided LCNF Fuzzer & P0 Trust Boundary ==="
python3 "$ROOT_DIR/scripts/run_conformance_suite.py" --tier C1,C4 --fuzz-seeds "${CONFORMANCE_SEEDS:-32}" --asan --ubsan
python3 -m unittest -v "$ROOT_DIR/scripts/test_p0_trust_boundary.py"
python3 -m unittest -v "$ROOT_DIR/scripts/test_kernel_gate_audit.py"
python3 "$ROOT_DIR/scripts/emitter_mutants.py" --unit-tests

echo "=== [7/9] Stage 2 LLVM Differential (lli), Alive2 Translation Validation & lean-mlir Bridge Gate ==="
python3 "$ROOT_DIR/scripts/run_llvm_lli_diff.py" --self-test
python3 "$ROOT_DIR/scripts/run_alive2_tv.py" --self-test
python3 "$ROOT_DIR/scripts/check_lean_mlir_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_lean_mlir_bridge_sync.py"
if command -v lli-18 >/dev/null 2>&1 || command -v lli >/dev/null 2>&1 || [ -x /usr/lib/llvm-18/bin/lli ]; then
  python3 "$ROOT_DIR/scripts/run_llvm_lli_diff.py" --core-bin "$CORE_BIN"
elif [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  echo "[FAIL] lli / lli-18 is required in CI for Stage 2A differential gate" >&2
  exit 1
else
  echo "  [SKIP] lli not installed locally; run_llvm_lli_diff.py --self-test passed (full suite enforced in CI)"
fi
if [ -n "${ALIVE_TV:-}" ] || command -v alive-tv >/dev/null 2>&1; then
  python3 "$ROOT_DIR/scripts/run_alive2_tv.py" --core-bin "$CORE_BIN"
elif [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  echo "[FAIL] alive-tv is required in CI for Stage 2B translation-validation gate" >&2
  exit 1
else
  echo "  [SKIP] alive-tv not installed locally; run_alive2_tv.py --self-test passed (full suite enforced in CI)"
fi

echo "=== [8/9] Stage 3 GPU/TPU Differential (ptxas, OpenXLA StableHLO, Metal MSL 3.0) & LNSym / Sail-RISC-V / ConLeche Bridge Gates ==="
python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --self-test
python3 "$ROOT_DIR/scripts/check_lnsym_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_lnsym_bridge_sync.py"
python3 "$ROOT_DIR/scripts/check_con_leche_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_con_leche_bridge_sync.py"
python3 "$ROOT_DIR/scripts/check_sail_riscv_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_sail_riscv_bridge_sync.py"
GPU_TPU_CACHE="${GPU_TPU_TOOLS_CACHE:-$HOME/.cache/gpu-tpu-tools}"
if [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --ensure-tools --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN"
elif ( [ -n "${PTXAS:-}" ] || command -v ptxas >/dev/null 2>&1 || [ -x "$GPU_TPU_CACHE/bin/ptxas" ] ) && \
     PYTHONPATH="${GPU_TPU_CACHE}/site-packages${PYTHONPATH:+:$PYTHONPATH}" python3 -c "from mlir.dialects import stablehlo" >/dev/null 2>&1; then
  python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN"
else
  echo "  [SKIP] ptxas / OpenXLA stablehlo wheel not cached locally; run_gpu_tpu_diff.py --self-test passed (full suite enforced in CI)"
fi

echo "=== [9/9] Stage 4 Target-IR 4-Backend Differential & Sanitizer/UB Fuzzing Gate ==="
python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --self-test
"$CORE_BIN" target-ir-fuzz-suite --self-test
FUZZ_SEEDS="${TARGET_IR_FUZZ_SEEDS:-16}"
if [ "$FUZZ_SEEDS" -gt 0 ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
    python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --ensure-tools --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN" --seeds "$FUZZ_SEEDS"
  elif ( command -v lli-18 >/dev/null 2>&1 || command -v lli >/dev/null 2>&1 || [ -x /usr/lib/llvm-18/bin/lli ] ) && \
       ( [ -n "${PTXAS:-}" ] || command -v ptxas >/dev/null 2>&1 || [ -x "$GPU_TPU_CACHE/bin/ptxas" ] ) && \
       PYTHONPATH="${GPU_TPU_CACHE}/site-packages${PYTHONPATH:+:$PYTHONPATH}" python3 -c "from mlir.dialects import stablehlo" >/dev/null 2>&1; then
    python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN" --seeds "$FUZZ_SEEDS"
  else
    echo "  [SKIP] lli / ptxas / OpenXLA stablehlo not all cached locally; run_target_ir_fuzz.py --self-test and target-ir-fuzz-suite --self-test passed (full 4-backend suite enforced in CI)"
  fi
fi

echo "=== LOCAL VALIDATION GATES PASSED (scalar corpus; full roadmap coverage remains open) ==="
