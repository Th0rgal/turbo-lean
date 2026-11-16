#!/usr/bin/env bash
# Local Mechanical Reviewer Checklist (Contract V5 in roadmap/VALIDATION_CONTRACTS.md)
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TOOLCHAIN="$(tr -d '[:space:]' < "$ROOT_DIR/lean/lean-toolchain")"
TOOLCHAIN_DIR="leanprover--lean4---${TOOLCHAIN#leanprover/lean4:}"
for cand in \
  "$ROOT_DIR/target/release" \
  "$ROOT_DIR/target/debug" \
  "${ELAN_HOME:-$HOME/.elan}/toolchains/$TOOLCHAIN_DIR/bin" \
  "${ELAN_HOME:-$HOME/.elan}/bin" \
  "${CARGO_HOME:-$HOME/.cargo}/bin" \
  "$HOME/.local/bin"; do
  if [ -d "$cand" ]; then
    PATH="$cand:$PATH"
  fi
done
export PATH

if [ -n "${TURBO_AUDITOR_BIN+x}" ]; then
  TURBO_BIN="$TURBO_AUDITOR_BIN"
  if [ -z "$TURBO_BIN" ] || [ ! -x "$TURBO_BIN" ]; then
    echo "[FAIL] TURBO_AUDITOR_BIN=${TURBO_BIN:-<empty>} is missing or not executable" >&2
    exit 1
  fi
else
  TURBO_BIN="$ROOT_DIR/target/release/turbo-lean"
  if [ ! -x "$TURBO_BIN" ]; then
    TURBO_BIN="$(command -v turbo-lean || true)"
  fi
fi
FULL_BIN="$ROOT_DIR/lean/.lake/build/bin/lean-native"
CORE_BIN="$ROOT_DIR/lean/.lake/build/bin/lean-native-core"
ZYGOTE_BIN="$ROOT_DIR/lean/.lake/build/bin/turbo-zygote"

if [ -z "$TURBO_BIN" ] || [ ! -x "$TURBO_BIN" ]; then
  echo "[FAIL] turbo-lean binary not found or not executable" >&2
  exit 1
fi
if [ ! -x "$FULL_BIN" ]; then
  echo "[FAIL] $FULL_BIN not found; build with (cd lean && lake build lean-native)" >&2
  exit 1
fi
if [ ! -x "$CORE_BIN" ]; then
  echo "[FAIL] $CORE_BIN not found; build with (cd lean && lake build lean-native-core)" >&2
  exit 1
fi
if [ ! -x "$ZYGOTE_BIN" ]; then
  echo "[FAIL] $ZYGOTE_BIN not found; build with (cd lean && lake build turbo-zygote)" >&2
  exit 1
fi

# Gates live in scripts/contract.d/ as per-gate fragments (HY1); they are
# sourced in lexicographic order into this shell, so they share the variables
# above and any failing command aborts the whole run exactly as before.
# The fragment list is expanded inside a subshell that exports LC_ALL=C, so
# the order cannot depend on the caller's locale; the gates themselves still
# run under whatever locale the caller set.

contract_fragments=()
while IFS= read -r contract_fragment; do
  contract_fragments+=("$contract_fragment")
done < <(cd "$ROOT_DIR" && export LC_ALL=C && printf '%s\n' scripts/contract.d/*.sh)

for contract_fragment in "${contract_fragments[@]}"; do
  source "$contract_fragment"
done

echo "=== LOCAL VALIDATION GATES PASSED (scalar + multi-module Lake C2 fixtures; full roadmap coverage remains open) ==="
