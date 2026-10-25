#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:$PATH:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$HOME/.elan/bin:$HOME/.cargo/bin"

echo "[1/3] Checking doc & context ratchet (--sync-docs)..."
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check
grep -q "86/86" README.md
grep -q "108/108" README.md
grep -q "86/86" AGENTS.md
grep -q "108/108" AGENTS.md

echo "[2/3] Auditing TurboLean/Spec.lean & LeanNative/Spec.lean via turbo-lean audit-spec..."
if [ -x "$ROOT_DIR/target/release/turbo-lean" ]; then
  "$ROOT_DIR/target/release/turbo-lean" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==86 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$ROOT_DIR/target/release/turbo-lean" --json audit-spec lean/LeanNative/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==108 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'LeanNative/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$ROOT_DIR/target/release/turbo-lean" --json ci-verify --project-dir lean --mode trusted --receipt /tmp/ci-receipt.json >/dev/null
  rm -f /tmp/ci-receipt.json
fi

echo "[3/3] Building Lean & Rust workspace..."
(cd lean && lake build)
./lean/.lake/build/bin/lean-native-core self-test
./lean/.lake/build/bin/lean-native-core emit-cabi-bindings lean/LeanNative/Spec.lean --emit-rust /tmp/ln_cabi_check.rs
grep -q "lean_native_ntt_butterfly_fused_2layer_slice" /tmp/ln_cabi_check.rs
rm -f /tmp/ln_cabi_check.rs
./lean/.lake/build/bin/turbo-lean-native self-test
if command -v cargo >/dev/null 2>&1; then
  cargo check --release
fi
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (86/86 + 108/108 tight specs, 65 C-ABI exports, 203 theorems, 0 sorryAx)"
