# clifv paired benchmark

Status: aborted. Telemetry: off.

A = stock `lake build FV`; B = `turbo-lean --no-daemon build FV`. Order: ABAB….
Ratio = arithmetic mean of paired stock/turbo wall times; values > 1 favor turbo.
CPU and RSS cover the timed command and waited-for children; detached daemons may be excluded.

## Provenance

```json
{
  "hostname": "3fc010451603",
  "platform": "Linux 3fc010451603 6.17.0-35-generic #35~24.04.1-Ubuntu SMP PREEMPT_DYNAMIC Tue May 26 19:30:42 UTC 2 x86_64",
  "nproc": 28,
  "mem_total_kib": 65675632,
  "load_before": [
    1.48095703125,
    1.26953125,
    1.10107421875
  ],
  "load_after": [
    19.84375,
    24.08837890625,
    22.55419921875
  ],
  "LEAN_NUM_THREADS": "12",
  "started_utc": "2026-11-01T06:18:17.007450+00:00",
  "clifv_sha": "5018b9509dc124154dbe08a5bd85862595d8eab7",
  "turbo_lean_sha": "0212d865be1a1093decef308225a0badcdccb526",
  "toolchain": "leanprover/lean4:v4.34.1",
  "turbo_binary": "/var/lib/orb-node/work/1496eb9d-03db-45f3-b9f5-6936ad9ef51d/turbo-lean/target/release/turbo-lean",
  "turbo_binary_sha256": "f027951c464151fe4ab751592f8101b1b9b5363e00382440f18163b482a72614",
  "turbo_version": "turbo-lean 0.1.0",
  "lean_version": "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)",
  "environment_overrides": {
    "TURBO_LEAN_TELEMETRY": "off",
    "TURBO_LEAN_HOME": "/var/lib/orb-node/work/1496eb9d-03db-45f3-b9f5-6936ad9ef51d/pairs1-work/turbo-cache",
    "TURBO_LEAN_STAGING_DIR": "/dev/shm/bench-clifv-999-8mxzzc34",
    "TURBO_LEAN_NO_DAEMON": "1",
    "TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK": "0",
    "TMPDIR": "/var/lib/orb-node/work/1496eb9d-03db-45f3-b9f5-6936ad9ef51d/pairs1-work/tmp",
    "ELAN_TOOLCHAIN": "leanprover/lean4:v4.34.1"
  },
  "daemon_stop": "command + owned-worker cleanup"
}
```

