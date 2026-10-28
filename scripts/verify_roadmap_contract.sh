#!/usr/bin/env bash
# 10-Second Mechanical Reviewer Checklist (Contract V5 in roadmap/VALIDATION_CONTRACTS.md)
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:$ROOT_DIR/target/debug:/var/lib/sandboxed-node/work/4c277c9d-4b85-4a1a-88ab-2c06bed519b1/warroom-tools/rust/rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.local/bin:$PATH"

TURBO_BIN="$(command -v turbo-lean || true)"
CORE_BIN="$ROOT_DIR/lean/.lake/build/bin/lean-native-core"

if [ -z "$TURBO_BIN" ]; then
  echo "[FAIL] turbo-lean binary not found on PATH" >&2
  exit 1
fi
if [ ! -x "$CORE_BIN" ]; then
  echo "[FAIL] $CORE_BIN not found; build with (cd lean && lake build lean-native-core)" >&2
  exit 1
fi

echo "=== [1/6] Spec & Documentation Pinning Ratchet (Contract V1) ==="
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check

echo "=== [2/6] Multi-Hop Vacuity, Tightness & Packing Audit (audit-spec v2) ==="
"$TURBO_BIN" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert d['tight_specs'] == d['total_specs_audited'] and d['tight_specs'] >= 86, d
assert len(d.get('droppable_hypotheses', [])) == 0, d
assert len(d.get('horizontal_packing_warnings', [])) == 0, d
print(f'  [OK] TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 droppable, 0 packing warnings)')
"
"$TURBO_BIN" --json audit-spec lean/LeanNative/Spec.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert d['tight_specs'] == d['total_specs_audited'] and d['tight_specs'] >= 116, d
assert len(d.get('droppable_hypotheses', [])) == 0, d
print(f'  [OK] LeanNative/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 droppable)')
"

echo "=== [3/6] In-Kernel Transitive Axiom Gate (Lean.collectAxioms) ==="
"$CORE_BIN" audit-axioms --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['passed'] is True, d
assert d['theoremsAudited'] >= 215, d
assert d['forbiddenAxiomsFound'] == [], d
print(f'  [OK] AxiomAudit: {d[\"theoremsAudited\"]} theorems verified in kernel (0 sorryAx, 0 trustCompiler)')
"

echo "=== [4/6] Verified Pass Contract Gate (Contract V2) ==="
grep -q "structure VerifiedCodePassContract" lean/LeanNative/Transform/Pass.lean
grep -q "def verifiedAlgebraicPeepholeContract : VerifiedCodePassContract" lean/LeanNative/Transform/AlgebraicOpt.lean
"$CORE_BIN" verify-certs --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['verified'] is True and d['overallAssurance'] == 'VerifiedKernelProof', d
print(f'  [OK] Pass Certificates: verified={d[\"verified\"]}, assurance={d[\"overallAssurance\"]}, decls={len(d[\"declSummaries\"])}')
"

echo "=== [5/6] Segregated Plugin & Adversarial Mutant Gate (Law 1) ==="
"$CORE_BIN" plugins --test-adversarial --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['adversarialRejected'] is True and d['rejectedCount'] >= 1, d
assert all(a['tvVerified'] for a in d['declAudits']), d
print(f'  [OK] Segregated Plugins: accepted={d[\"acceptedCount\"]}, rejected={d[\"rejectedCount\"]}, adversarialRejected={d[\"adversarialRejected\"]}')
"

echo "=== [6/6] 3-Way Differential Conformance Suite (Contract V4) ==="
python3 "$ROOT_DIR/scripts/run_conformance_suite.py"

echo "=== ALL 6 ROADMAP VALIDATION CONTRACTS PASSED ==="
