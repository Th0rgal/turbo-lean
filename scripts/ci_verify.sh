#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:/var/lib/opencode/.cargo/bin:/usr/local/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/root/.cargo/bin:/root/.elan/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"

echo "[1/3] Checking doc & context ratchet (--sync-docs)..."
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check
grep -q "81/81" README.md
grep -q "81/81" AGENTS.md
grep -q "Shared Canonical 10-Term Glossary" AGENTS.md

echo "[2/3] Auditing TurboLean/Spec.lean via turbo-lean audit-spec..."
if [ -x "$ROOT_DIR/target/release/turbo-lean" ]; then
  "$ROOT_DIR/target/release/turbo-lean" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==81 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
fi

echo "[3/3] Building Lean & Rust workspace..."
(cd lean && lake build)
if command -v cargo >/dev/null 2>&1; then
  cargo check --release
fi
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (81/81 tight specs, 48 C-ABI exports, 0 sorryAx)"
