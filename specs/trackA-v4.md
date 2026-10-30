# Track A — spec v4 (quorum decision D2 = option B, unanimous: Astra, carbon-4; 2026-10-30)

Declaration-level kernel-check reuse (A2'') is DROPPED from scope; its transfer theorem is
BLOCKED_MISSING_DEPENDENCY (lean4lean: AddInduct empty, VInductDecl.WF/proj/recursor sorry; stock kernel has
non-declarative acceptance inputs: LEAN_NAT_MAX_SIZE, module-mode reduceBool, unit-like eta). A1 stays SUSPENDED.
Statement hashes never authorize skipping stock kernel checks.

## Work items (one PR each; file ownership disjoint)
A0a (pr_verify.rs, splitter.rs statement-hash path, check.rs, Lean zygote helper):
  - Kernel-level statement digests for `pr-verify --disallow-statement-changes` / statement pinning: digest of
    elaborated `ConstantInfo` (ordered levelParams + type) per theorem, plus digest of the IF-closure of
    constants in the type (definitions referenced by the statement), computed from built .oleans of base and head.
  - Fixtures: adding an `import` / whitespace / comment edit in a touched file → 0 statement-edited theorems;
    changing a def referenced in a theorem's type → reported; changing the theorem's type → reported;
    `--scope <dir>` → 0 out-of-scope reports.
  - Project allowlist policy (turbo-lean.toml, resolved at --base) admits audited `@[csimp]` and the
    project's `native_decide` aux axioms; still fails closed on sorryAx, Lean.trustCompiler, unallowed axioms.
A0b (server.rs, zygote.rs, daemon lifecycle, timeout plumbing):
  - `turbo-lean daemon stop`, `--no-daemon` one-shot mode, idle TTL self-exit; per-invocation `check --timeout`
    reaches an already-running worker without restart. Integration test: 0 orphan serve/turbo_zygote PIDs and
    /dev/shm staging cleaned after exit/TTL.
A0c (lake_build.rs worktree linking, telemetry config):
  - Opt-out of auto worktree hard-linking (`--no-auto-worktree-link`, `[worktree] auto_link = false`,
    env TURBO_LEAN_NO_WORKTREE_LINK=1): 0 links/copies from the main clone, 0 permission mutations of .lake files.
  - Telemetry: remote emission strictly opt-in; test asserts 0 outbound requests without explicit opt-in.
A0d (after A0a merges; splitter.rs shard discovery):
  - `check --decl` regression corpus from clifv @5018b95 constructs: `set_option … in theorem`, private/protected,
    scoped attributes, have-heavy proofs, decide +kernel, bv_decide, native_decide witnesses (allowed by policy):
    100% declaration-discovery parity with the elaborated environment (shard list vs `env.constants` theorems of
    the module); verdict parity with stock Lean on injected broken proofs.
A0e bench script `scripts/bench_clifv.sh` (paired, sequential, alternating, records CV) + doc.
A3 (after A0a–A0d): clifv shadow-mode CI PR (opened by us, never merged by us), non-blocking, 20 consecutive
  main commits window recorded with 0 unresolved correctness discrepancies vs stock.

## Exit criterion (Track A)
All A0 items merged on turbo-lean main with CI green and fixtures in CI logs; A3 PR opened with its 20-commit
shadow record; performance verdict published from paired measurements (B-1 re-run on a non-archiving node, and
B-2c as an optimistic opportunity estimate only). Claim acceleration only where demonstrated.
