#!/usr/bin/env bash
set -euo pipefail
export HOME="/var/lib/orb-node/work/1496eb9d-03db-45f3-b9f5-6936ad9ef51d"
export ELAN_HOME="/var/lib/orb-node/work/caches/elan"
export CARGO_HOME="$HOME/.cargo"
export RUSTUP_HOME="$HOME/.rustup"
export PATH="$HOME/.local/bin:$CARGO_HOME/bin:$ELAN_HOME/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
unset TURBO_LEAN_COMPUTE_NODES LEAN_NATIVE_COLAB_API_URL LEAN_NATIVE_COLAB_TOKEN TURBO_LEAN_SSH_GPU_HOST || true
export SANDBOXED_ALLOW_RAW_LAKE=1
export TURBO_LEAN_TELEMETRY=off
export LEAN_NUM_THREADS=12
export TURBO_LEAN_JOBS=12
export TURBO_LEAN_MAX_MEMORY_MB=53248
export REAL_GNU_TIME="$HOME/.local/bin/time"
export PYTHONPATH="$HOME/.local/pycustomize"

"$HOME/bench-meta/loadlog.sh" "BEFORE-pairs1"
date -u +%FT%TZ > "$HOME/bench-meta/pairs1_start.txt"

set +e
"$HOME/turbo-lean/scripts/bench_clifv.sh" \
  --turbo "$HOME/turbo-lean/target/release/turbo-lean" \
  --turbo-repo "$HOME/turbo-lean" \
  --lake "$ELAN_HOME/bin/lake" \
  --repo "$HOME/clifv-full.git" \
  --sha 5018b95 \
  --scenarios cold,warm \
  --pairs 1 \
  --work-dir "$HOME/pairs1-work" \
  --output "$HOME/pairs1-results"
RC=$?
set -e

echo "EXIT=$RC" > "$HOME/bench-meta/pairs1_exit.txt"
date -u +%FT%TZ >> "$HOME/bench-meta/pairs1_exit.txt"
"$HOME/bench-meta/loadlog.sh" "AFTER-pairs1"
exit "$RC"
