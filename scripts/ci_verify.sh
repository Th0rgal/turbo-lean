#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:$PATH:$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$HOME/.elan/bin:$HOME/.cargo/bin"

TURBO_BIN="${TURBO_AUDITOR_BIN:-$ROOT_DIR/target/release/turbo-lean}"
if [ ! -x "$TURBO_BIN" ]; then
  echo "[FAIL] Missing turbo-lean auditor: $TURBO_BIN" >&2
  exit 1
fi

echo "[1/3] Checking doc & context ratchet (--sync-docs)..."
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check

echo "[2/3] Auditing TurboLean/Spec.lean & LeanNative/Spec.lean via turbo-lean audit-spec..."
if [ -x "$TURBO_BIN" ]; then
  "$TURBO_BIN" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==d['total_specs_audited'] and d['tight_specs']>=87 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$TURBO_BIN" --json audit-spec lean/LeanNative/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==d['total_specs_audited'] and d['tight_specs']>=110 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'LeanNative/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$TURBO_BIN" --json ci-verify --project-dir lean --mode trusted --receipt /tmp/ci-receipt.json >/dev/null
  rm -f /tmp/ci-receipt.json
fi

echo "[2b/3] Checking HeapObj contract clause→regression table (docs/HEAPOBJ_CONTRACT.md)..."
python3 - <<'PY'
import re
src = open("lean/LeanNative/Tests/HeapObjContract.lean").read()
doc = open("docs/HEAPOBJ_CONTRACT.md").read()
marks = re.findall(r"^-- REGRESSION\((\w+)\)\n(-- XFAIL\(heapobj-contract\): flips in 5b)?", src, re.M)
code = {n: bool(x) for n, x in marks}
assert len(code) == len(marks), "duplicate REGRESSION names"
rows = re.findall(r"^\|[^|]*\| `(\w+)` \| (pass|XFAIL) \|$", doc, re.M)
table = {n: s == "XFAIL" for n, s in rows}
assert code == table, f"contract table out of sync: module={code} doc={table}"
assert src.count("XFAIL(heapobj-contract): flips in 5b") == sum(code.values()) + 1, "stray/unmarked XFAIL"
unc = re.findall(r"^-- UNCOVERED\(([\w.-]+)\):", src, re.M)
unc_doc = re.findall(r"^\| `([\w.-]+)` \| [^|]+ \|$", doc.split("### UNCOVERED clauses", 1)[1], re.M)
assert len(unc) == len(set(unc)) and set(unc) == set(unc_doc), f"UNCOVERED list out of sync: module={unc} doc={unc_doc}"
print(f"HeapObj contract: {len(code)} regressions, {sum(code.values())} explicit XFAIL (flip in 5b), {len(unc)} UNCOVERED")
PY

echo "[3/3] Building Lean & Rust workspace..."
(cd lean && lake build)
./lean/.lake/build/bin/lean-native-core self-test
./lean/.lake/build/bin/lean-native-core emit-cabi-bindings lean/LeanNative/Spec.lean --emit-rust /tmp/ln_cabi_check.rs --emit-swift /tmp/ln_cabi_check.swift --emit-modulemap /tmp/ln_cabi_check.modulemap
grep -q "lean_native_ntt_butterfly_fused_2layer_slice" /tmp/ln_cabi_check.rs
grep -q "pub unsafe fn leannative_verify_rc_mode_safe" /tmp/ln_cabi_check.rs
grep -q "@_silgen_name(\"leannative_verify_rc_mode_safe\")" /tmp/ln_cabi_check.swift
grep -q "module TurboLeanCABI" /tmp/ln_cabi_check.modulemap
rm -f /tmp/ln_cabi_check.rs /tmp/ln_cabi_check.swift /tmp/ln_cabi_check.modulemap
./lean/.lake/build/bin/turbo-lean-native self-test
cargo check --locked --release -j 1
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (0 sorryAx)"
