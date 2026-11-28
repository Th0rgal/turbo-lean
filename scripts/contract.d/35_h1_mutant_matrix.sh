echo "=== [3b/10] H1 Mutant Kill Matrix, SpecLocked Pin & Coverage Ratchet (W2-H1.4) ==="
"$CORE_BIN" audit-axioms --json \
  | python3 "$ROOT_DIR/scripts/h1_mutant_matrix.py" --audit-json - --with-coverage-ratchet
python3 "$ROOT_DIR/scripts/test_h1_mutant_matrix.py"
