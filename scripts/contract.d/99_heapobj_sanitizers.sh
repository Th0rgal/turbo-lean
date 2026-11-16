echo "=== [10/10] Stage 5 Unwrapped libleanrt.a HeapObj/ABI ASan/LSan/UBSan & TSan Stress Gate ==="
python3 "$ROOT_DIR/scripts/run_heapobj_abi_sanitizers.py" --self-test
if [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  python3 "$ROOT_DIR/scripts/run_heapobj_abi_sanitizers.py" --core-bin "$CORE_BIN" --require-tsan
else
  python3 "$ROOT_DIR/scripts/run_heapobj_abi_sanitizers.py" --core-bin "$CORE_BIN"
fi
