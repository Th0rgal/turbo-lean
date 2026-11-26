# Why warm (daemon) modes failed under the namespace wrapper, and the fix

Symptom (both full runs, 900 s and 2400 s per-check budgets): every cold mode
measured; every warm mode recorded None, and one workload's warm setup ran to
the budget cap. Logs: bench.out, bench-2400.out.

Isolation (diag/, three cells, one warm check each):
- ns (wrapper as in run_bench.sh): exit 1, "Failed to establish a verified
  private (0700) temporary scratch root" (crates/turbo-lean/src/check/identity.rs:76).
- host (no wrapper, same env otherwise): exit 0, verdict in 6.4 s.
- ns2 (wrapper plus TMPDIR pointing at a directory created inside the
  namespace): exit 1, same error — TMPDIR does not cure it.

Mechanism: verified_private_temp_scratch_base (identity.rs:71-78) accepts a
scratch base only when every ancestor directory is owned by root or the
current user. Inside an unprivileged user namespace the ancestor chain of any
path (/, /mnt, ...) appears owned by an unmapped user id, so the check can
never pass, whatever TMPDIR names. Cold (no-daemon) checks never build this
scratch base, which is why only warm modes failed.

Decision: the wrapper's only purpose was keeping the machine's real hostname
out of the recorded results JSON (bench_check_loop.py records platform.node()
in the host block). The bench script now records the --machine-label value as
the hostname field when a label is given, so the wrapper is unnecessary and
warm modes run on the plain host. Rejected alternatives: relaxing the
ownership verification (touches trust logic for a bench convenience), and
keeping the wrapper with a pre-created scratch mount (cannot fix the ancestor
chain without privileges).

Measurement runs use run_bench_plain.sh (no wrapper, label g2a-ro-192c,
per-check budget 2400 s).
