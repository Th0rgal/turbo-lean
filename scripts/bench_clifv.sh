#!/usr/bin/env bash
# Keep this local to the benchmark process and its children.
set -euo pipefail
export TURBO_LEAN_TELEMETRY=off
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/bench_clifv.py" "$@"
