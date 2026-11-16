echo "=== [6/10] 3-Way Differential Conformance Suite (C1, Provisioned C2 Lake Packages, C4), Grammar-Guided LCNF Fuzzer & P0 Trust Boundary ==="
python3 "$ROOT_DIR/scripts/run_conformance_suite.py" --tier C1,C2,C4 --c2-packages-dir auto --fuzz-seeds "${CONFORMANCE_SEEDS:-32}" --asan --ubsan
python3 -m unittest -v "$ROOT_DIR/scripts/test_p0_trust_boundary.py"
python3 -m unittest -v "$ROOT_DIR/scripts/test_kernel_gate_audit.py"
python3 "$ROOT_DIR/scripts/emitter_mutants.py" --unit-tests
