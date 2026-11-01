#!/bin/bash
. /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/env.sh
unset TURBO_LEAN_COMPUTE_NODES LEAN_NATIVE_COLAB_API_URL LEAN_NATIVE_COLAB_TOKEN
export SANDBOXED_ALLOW_RAW_LAKE=1
# uruk caps every node job at 16 GiB (SANDBOXED_NODE_JOB_MEMORY_BYTES); the default 8-way
# lake/lean parallelism exceeded it (diag/). Cap parallelism identically for both arms.
export LEAN_NUM_THREADS=3 TURBO_LEAN_JOBS=3 TURBO_LEAN_MAX_MEMORY_MB=14336
cd /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/repo
date -u +%FT%TZ > /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench3/start.txt
scripts/bench_clifv.sh --turbo /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/repo/target/release/turbo-lean --turbo-repo /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/repo \
  --lake $ELAN_HOME/bin/lake --scenarios cold,warm --pairs 2 --sha 5018b95 \
  --work-dir /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench3/work --output /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench3/results
echo "EXIT=$?" > /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench3/exit.txt; date -u +%FT%TZ >> /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench3/exit.txt
/var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/meta/loadlog.sh AFTER-bench
