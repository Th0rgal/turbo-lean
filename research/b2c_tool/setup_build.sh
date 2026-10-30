#!/usr/bin/env bash
# Source after env.sh. Isolated shim; shared toolchain is never modified.
set -euo pipefail
b2c_tool_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
export B2C_REAL_ROOT="$ELAN_HOME/toolchains/leanprover--lean4---v4.34.1"
export B2C_REAL_LEAN="$B2C_REAL_ROOT/bin/lean"
export B2C_LOCK_DIR="$b2c_tool_dir/../../../.b2c-locks"
export B2C_SHIM="$b2c_tool_dir/../../../.b2c-sysroot"
mkdir -p "$B2C_SHIM/bin" "$b2c_tool_dir/../../../.b2c-bin"
for b2c_entry in "$B2C_REAL_ROOT"/*; do
  [ "$(basename "$b2c_entry")" = bin ] || ln -sfn "$b2c_entry" "$B2C_SHIM/$(basename "$b2c_entry")"
done
for b2c_entry in "$B2C_REAL_ROOT"/bin/*; do
  [ "$(basename "$b2c_entry")" = lean ] || ln -sfn "$b2c_entry" "$B2C_SHIM/bin/$(basename "$b2c_entry")"
done
ln -sfn "$b2c_tool_dir/lean_wrap.py" "$B2C_SHIM/bin/lean"
cat > "$b2c_tool_dir/../../../.b2c-bin/lake" <<'WRAP'
#!/usr/bin/env bash
set -euo pipefail
if [ "${1:-}" = -j4 ]; then shift; fi
exec "$B2C_REAL_ROOT/bin/lake" "$@"
WRAP
chmod +x "$b2c_tool_dir/../../../.b2c-bin/lake" "$b2c_tool_dir/lean_wrap.py"
export LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$B2C_SHIM"
export PATH="$b2c_tool_dir/../../../.b2c-bin:$PATH"
export LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
unset FV_LAKE_CACHE LAKE_CACHE_DIR || true
