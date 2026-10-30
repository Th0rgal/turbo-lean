#!/usr/bin/env bash
export ELAN_HOME=/var/lib/sandboxed-node/caches/elan
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=4
export FV_MEMCAP=16G

# Four-job baseline exceeded 16G; serialize module builds while retaining the cap.
export B2C_MAX_ACTIVE=1
