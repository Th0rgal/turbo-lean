#!/bin/bash
/var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/meta/loadlog.sh DURING-run2-start
while [ ! -f /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/bench2/exit.txt ]; do sleep 1800; /var/lib/sandboxed-node/work/88fd3dc8-2d05-4816-9c09-40950a5c391a/meta/loadlog.sh DURING; done
