# B2c measurement — in progress

No avoidance percentages are available yet. The first of 20 commits is building. Its first attempt was stopped by the 16 GiB cap after 262 completed-module timing records; the build is resuming from those artifacts with one active module at a time.

Scope: the import cone of `FV.Backend.Proof.{DefGenTab,IselSzTab,IselCtlTry}` and `FV.Opt.Proof.RuleArith`, not all FV. Commits are the 20 first-parent commits ending at `5018b95`, in oldest-first order.

Declaration-level reuse will be reported as an **OPTIMISTIC UPPER BOUND ONLY**. The requested key is incomplete: it omits `LEAN_NAT_MAX_SIZE`, module-mode `Lean.reduceBool` axiom information, unit-like eta dependencies through constructor field counts, and implicit Bool/Nat dependencies. This is a diagnostic measurement, not a sound cache design.

All required hash fixtures pass: proposition-body changes propagate into theorem IF; level-parameter order affects IF; proof changes affect K while preserving IF. Lean extracts explicit expression DAGs; the Python companion computes deterministic SHA-256 and SCC closure. `Expr.hash` is not a digest.

A custom replay driver calls `Lean.Kernel.Environment.addDecl`, including unsafe/partial definitions. Inductives and recursive unsafe/partial definitions are reconstructed as kernel declaration groups. Constructors and recursors are checked against the kernel-generated results. Duplicate theorems are rechecked under a fresh name, not skipped. A native clock reads thread CPU nanoseconds around each call; replay overhead is recorded separately and summed kernel CPU must not exceed total replay CPU. The `Init.Prelude` validation replay passed (2,033 calls over 2,324 constants). Full `Init` validation covers 66,317 rows and 64,849 kernel calls, including 130 duplicate theorems rechecked. The summed row times exactly match summed kernel CPU. Valid fixture declarations also pass the kernel, and two fresh Lean processes produce identical fixture serializations and hashes.

Resources: `LEAN_NUM_THREADS=4`, `FV_MEMCAP=16G`, at most four active Lean module builds initially; one at a time after the baseline cap failure. Lake v4.34.1 rejects `-j4`; a local wrapper accepts it and enforces the four-process bound with a semaphore. Per-module build timing excludes semaphore waiting. No shared toolchain files are changed.

Remaining: finish baseline and 19 incremental builds, extract and replay each commit, push each completed commit's data, calculate dependent-module cutoff and optimistic kernel reuse with kind/module splits and concrete examples, then audit the complete report.
