echo "=== [4/10] Verified Pass Contract & Bridge/CoreCLI Hygiene Gate (Contract V2, M4 & M5) ==="
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
