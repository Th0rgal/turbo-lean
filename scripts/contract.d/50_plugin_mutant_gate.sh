echo "=== [5/10] Segregated Plugin & Adversarial Mutant Gate (Law 1) ==="
"$CORE_BIN" plugins --canonical-benchmark --test-adversarial --json | python3 -c "
import json, sys
d = json.load(sys.stdin)
assert d['adversarialRejected'] is True and d['rejectedCount'] >= 1, d
assert all(a['tvVerified'] for a in d['declAudits']), d
print(f'  [OK] Segregated Plugins: accepted={d[\"acceptedCount\"]}, rejected={d[\"rejectedCount\"]}, adversarialRejected={d[\"adversarialRejected\"]}')
"
