#!/bin/bash
# snapshot: $1 = label
out=/var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/meta/load.log
{ echo "=== $(date -u +%Y-%m-%dT%H:%M:%SZ) [$1]"; uptime; free -m | sed -n 2p; ps aux --sort=-%cpu | head -11 | cut -c1-250; echo; } >> "$out"
