echo "=== [9/10] Stage 4 Target-IR 4-Backend Differential & Sanitizer/UB Fuzzing Gate ==="
TARGET_IR_FUZZ_STRICT_TOOLS="${CI:-${GITHUB_ACTIONS:-}}" python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --self-test
"$CORE_BIN" target-ir-fuzz-suite --self-test
FUZZ_SEEDS="${TARGET_IR_FUZZ_SEEDS:-16}"
if [ "$FUZZ_SEEDS" -le 0 ]; then
  echo "  [FAIL] TARGET_IR_FUZZ_SEEDS must be > 0 (got $FUZZ_SEEDS)" >&2
  exit 1
fi
if [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --ensure-tools --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN" --seeds "$FUZZ_SEEDS"
elif ( command -v lli-18 >/dev/null 2>&1 || command -v lli >/dev/null 2>&1 || [ -x /usr/lib/llvm-18/bin/lli ] ) && \
     ( [ -n "${PTXAS:-}" ] || command -v ptxas >/dev/null 2>&1 || [ -x "$GPU_TPU_CACHE/bin/ptxas" ] ) && \
     ( PYTHONPATH="${GPU_TPU_CACHE}/site-packages${PYTHONPATH:+:$PYTHONPATH}" python3 -c "from mlir.dialects import stablehlo" >/dev/null 2>&1 || \
       ( [ -x "$GPU_TPU_CACHE/python312/python/bin/python3" ] && \
         PYTHONPATH="${GPU_TPU_CACHE}/site-packages${PYTHONPATH:+:$PYTHONPATH}" "$GPU_TPU_CACHE/python312/python/bin/python3" -c "from mlir.dialects import stablehlo" >/dev/null 2>&1 ) ); then
  python3 "$ROOT_DIR/scripts/run_target_ir_fuzz.py" --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN" --seeds "$FUZZ_SEEDS"
else
  echo "  [SKIP] lli / ptxas / OpenXLA stablehlo not all cached locally; run_target_ir_fuzz.py --self-test and target-ir-fuzz-suite --self-test passed (full 4-backend suite enforced in CI)"
fi
