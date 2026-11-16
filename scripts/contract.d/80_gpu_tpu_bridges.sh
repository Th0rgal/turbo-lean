echo "=== [8/10] Stage 3 GPU/TPU Differential (ptxas, OpenXLA StableHLO, Metal MSL 3.0) & LNSym / Sail-RISC-V / ConLeche Bridge Gates ==="
python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --self-test
python3 "$ROOT_DIR/scripts/check_lnsym_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_lnsym_bridge_sync.py"
python3 "$ROOT_DIR/scripts/check_con_leche_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_con_leche_bridge_sync.py"
python3 "$ROOT_DIR/scripts/check_sail_riscv_bridge_sync.py" --self-test
python3 "$ROOT_DIR/scripts/check_sail_riscv_bridge_sync.py"
GPU_TPU_CACHE="${GPU_TPU_TOOLS_CACHE:-$HOME/.cache/gpu-tpu-tools}"
if [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${CI:-}" = "true" ]; then
  python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --ensure-tools --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN"
elif ( [ -n "${PTXAS:-}" ] || command -v ptxas >/dev/null 2>&1 || [ -x "$GPU_TPU_CACHE/bin/ptxas" ] ) && \
     PYTHONPATH="${GPU_TPU_CACHE}/site-packages${PYTHONPATH:+:$PYTHONPATH}" python3 -c "from mlir.dialects import stablehlo" >/dev/null 2>&1; then
  python3 "$ROOT_DIR/scripts/run_gpu_tpu_diff.py" --tools-cache-dir "$GPU_TPU_CACHE" --core-bin "$CORE_BIN"
else
  echo "  [SKIP] ptxas / OpenXLA stablehlo wheel not cached locally; run_gpu_tpu_diff.py --self-test passed (full suite enforced in CI)"
fi
