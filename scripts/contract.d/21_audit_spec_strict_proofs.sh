echo "=== [2b/10] Configurable Anti-Reward-Hacking & Shadow-Namespace Gate (audit-spec v2.1, Contract V1/V2/V3) ==="
"$TURBO_BIN" --json audit-spec --policy strict-proofs lean/LeanNative/Proofs/ lean/LeanNative/Transform/ lean/TurboLean/ConLeche.lean lean/TurboLean/ElabAudit.lean | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['ok'] and d['vacuous_specs'] == 0 and d['trivial_specs'] == 0, d
assert len(d.get('forbidden_scope_decls', [])) == 0, d
assert len(d.get('stub_defs', [])) == 0, d
print(f'  [OK] audit-spec v2.1 (strict-proofs) on M2-M5 proof & transform modules: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} tight (0 vacuous, 0 trivial, 0 stub_defs, 0 forbidden_scope_decls)')
"
