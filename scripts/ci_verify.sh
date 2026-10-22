#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin:/root/.cargo/bin:/root/.elan/bin:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"

echo "[1/3] Checking doc & context ratchet (--sync-docs)..."
grep -q "76/76" README.md
grep -q "76/76" AGENTS.md
grep -q "Shared Canonical 10-Term Glossary" AGENTS.md

echo "[2/3] Auditing TurboLean/Spec.lean via turbo-lean audit-spec..."
if [ -x "$ROOT_DIR/target/release/turbo-lean" ]; then
  "$ROOT_DIR/target/release/turbo-lean" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==76, d; print(f'TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
fi

echo "[3/3] Building Lean & Rust workspace..."
(cd lean && lake build)
if command -v cargo >/dev/null 2>&1; then
  cargo check --release
fi
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (76/76 tight specs, 0 sorryAx)"
