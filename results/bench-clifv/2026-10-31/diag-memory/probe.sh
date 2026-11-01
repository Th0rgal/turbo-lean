#!/bin/bash
# Diagnostic only (not a measurement): resume the dead attempt-2 stock prime and sample this job's cgroup memory.
. /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/env.sh
unset TURBO_LEAN_COMPUTE_NODES LEAN_NATIVE_COLAB_API_URL LEAN_NATIVE_COLAB_TOKEN
export LEAN_NUM_THREADS=${PROBE_THREADS:-4} SANDBOXED_ALLOW_RAW_LAKE=1 ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
D=/var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/diag
CG=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
echo "cg=$CG max=$(cat $CG/memory.max) LEAN_NUM_THREADS=${LEAN_NUM_THREADS-unset}" > $D/mem.log
( while true; do echo "$(date -u +%T) cur=$(( $(cat $CG/memory.current)/1048576 ))MiB peak=$(( $(cat $CG/memory.peak 2>/dev/null || echo 0)/1048576 ))MiB nlean=$(pgrep -c -f 'v4.34.1/bin/lean ') $(tr '\n' ' ' < $CG/memory.events)" >> $D/mem.log; sleep 10; done ) &
cd /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench2/work/stock
$ELAN_HOME/bin/lake build FV > $D/lake.log 2>&1
echo "lake exit $?" >> $D/mem.log
