echo "=== [3b/10] H1.1 Differential LCNF Interpreter Gate (RealLCNFSemantics vs compiled Lean reference) ==="
"$FULL_BIN" eval-lcnf --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['mismatch_count'] == 0, d
assert d['compared_count'] >= 12, d
assert d['compared_vectors'] >= 100, d
assert d['reference_evaluates_project_refuses_count'] >= 1, d
assert len(d['constructs_covered']) >= 20, d
for reason in ('non_computable', 'io', 'higher_order_or_closures', 'unsupported_construct'):
    assert d['skipped_by_reason'].get(reason, 0) >= 1, (reason, d['skipped_by_reason'])
print(f'  [OK] eval-lcnf differential: compared={d[\"compared_count\"]} vectors={d[\"compared_vectors\"]} agreed_failures={d[\"agreed_failure_count\"]} mismatches={d[\"mismatch_count\"]} constructs={len(d[\"constructs_covered\"])}')
"
