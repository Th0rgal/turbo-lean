echo "=== [7/10] Stage 2 LLVM Differential (lli), Alive2 Translation Validation & lean-mlir Bridge Gate ==="
python3 "$ROOT_DIR/scripts/run_llvm_lli_diff.py" --self-test
python3 "$ROOT_DIR/scripts/run_alive2_tv.py" --self-test
python3 "$ROOT_DIR/scripts/check_lean_mlir_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_lean_mlir_bridge_sync.py"
if command -v lli-18 >/dev/null 2>&1 || command -v lli >/dev/null 2>&1 || [ -x /usr/lib/llvm-18/bin/lli ]; then
  python3 "$ROOT_DIR/scripts/run_llvm_lli_diff.py" --core-bin "$CORE_BIN"
elif [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  echo "[FAIL] lli / lli-18 is required in CI for Stage 2A differential gate" >&2
  exit 1
else
  echo "  [SKIP] lli not installed locally; run_llvm_lli_diff.py --self-test passed (full suite enforced in CI)"
fi
if [ -n "${ALIVE_TV:-}" ] || command -v alive-tv >/dev/null 2>&1; then
  python3 "$ROOT_DIR/scripts/run_alive2_tv.py" --core-bin "$CORE_BIN"
elif [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  echo "[FAIL] alive-tv is required in CI for Stage 2B translation-validation gate" >&2
  exit 1
else
  echo "  [SKIP] alive-tv not installed locally; run_alive2_tv.py --self-test passed (full suite enforced in CI)"
fi
