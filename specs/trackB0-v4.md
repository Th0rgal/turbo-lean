# Track B0 — spec v4 (v3 + Q3: Astra & carbon-4 APPROVE_WITH_CHANGES; required changes folded in, marked [Q3])

## Deliverables (one PR; README table in a separate Boss PR)
1. Emitter mutation runner `scripts/emitter_mutants.py` + `scripts/emitter_mutants.json`:
   - 11 B-3 mutations as exact (file, search, replace, expected_match_count) patches; mismatch → APPLY_FAILED.
   - Pinned checks C1..C7 with exact commands. The runner REBUILDS every artifact a check depends on
     (lake build, cargo build --release, lean-native-core exe) inside each mutant run before running the
     check; stale binaries are impossible by construction (record build ids/hashes per run).
   - Baseline: ALL pinned checks must pass on baseline; any baseline failure → whole run INFRA_FAILED
     (never silently excluded).
   - Outcome per mutation ∈ {KILLED, SURVIVED, APPLY_FAILED, INFRA_FAILED}; INFRA_FAILED only for runner/tool
     failures identified by an explicit signature list (OOM, network, toolchain download), else a non-zero exit
     is a kill. A run with < 9 of 11 mutations in {KILLED, SURVIVED} is INCONCLUSIVE.
   - Fixtures: build-breaking mutation → KILLED; comment-only → SURVIVED; non-matching → APPLY_FAILED;
     a mutation that only breaks a runtime conformance check (not compilation) → KILLED by C5 (proves C5
     runs the rebuilt emitter).
2. CI job `emitter-mutation-report` (kill rate non-blocking) uploading JSON + logs.
3. Shadow-semantics checker `scripts/check_shadow_semantics.lean`:
   - pinned inventory: modules `LeanNative.Backend.Semantics`, `LeanNative.IR.LCNF`, `TurboLean.ConLeche`,
     and namespaces `LeanMLIR`, `LNSym`, `ConLeche`, `LCNF`; missing/unimported → fail; the inventory file is
     protected: CODEOWNERS on it and on the checker.
   - traversal over types, values, `.proj` (adds structure + ctor), recursor rules (`RecursorRule.rhs`),
     equation/matcher/`_unsafe_rec`/`match_n` auxiliaries; cycle detection; reports ≤3-hop and unbounded.
   - forbidden set: `LeanNative.Semantics.{evalCode, evalExpr, evalBinOp, evalUnaryOp, evalScalarExpr,
     evalLetValue}` and their private helpers.
   - clone check: canonicalize bodies by (i) delta-unfolding local `match_n`/aux constants of the definition
     being hashed, (ii) instantiating level params, (iii) erasing mdata/binder names; compare against the same
     canonical hash of each forbidden evaluator body (NOT of shared utilities such as `UInt64.add`). Scope stated
     as "verbatim / alpha-equivalent copies"; eta/let/arm-reordering evasions are out of scope and documented.
   - fixtures: direct call → fail; verbatim source copy of `evalBinOp` (with its `match`) under a new name → fail;
     BitVec-only namespace → pass; second new violation inside an already-allowlisted namespace → ratchet fails.
4. Ratchet (BLOCKING): violation identity = (target declaration, forbidden constant, kind∈{call≤3, call∞, clone}).
   CI reads the allowlist from `git show $BASE_SHA:scripts/shadow_allowlist.json` (on push to main: the parent
   commit); fails if the current set ⊄ base allowlist; also fails if a PR ADDS entries to the allowlist file.
   Initial allowlist entries are enumerated in the PR body and each one audited by hand (file:line).
5. README "Backend assurance" table (Boss PR): rows LLVM IR, C-ABI C99, C-ABI Rust, PTX, MLIR, Metal,
   TPU/StableHLO, AArch64 NEON kernel. "verified" requires a theorem whose statement is about the PRODUCTION
   emitter function used by the CLI for that target (name it, file:line) relating source semantics to emitted
   artifact semantics, with assumptions listed; "translation-validated" requires a per-compile checker whose
   soundness theorem is cited; otherwise "tested". Acceptance: every row present; each link resolves.

## Acceptance (mechanical)
- Runner fixtures pass; CI artifact on main reproduces B-3 baseline per mutation (exact outcome equality for
  all mutations that are KILLED/SURVIVED in both; any difference blocks the PR until re-run or root-caused).
- Checker fixtures pass; on main it reports exactly the enumerated, hand-audited allowlist; ratchet fixtures
  (new violation, allowlist addition) are shown failing in CI logs.
- No change to any emitter or proof file.

## [Q3] Required changes folded in
- Runner rebuilds and hashes ALL default Lake targets incl. both `lean-native` and `lean-native-core`, plus
  `target/release/turbo-lean`, inside every mutant run.
- Acceptance run must be CONCLUSIVE: on main all 11 mutations are applied (0 APPLY_FAILED) and all 11 outcomes are in
  {KILLED, SURVIVED} (0 INFRA_FAILED), except mutations proven NOT_APPLICABLE by evidence recorded in the JSON (e.g. a
  removed emitter); the comparison universe is fixed in advance (the 11 ids) and missing comparisons fail acceptance.
- Clone check canonicalization unfolds ALL matcher declarations (`Lean.Meta.isMatcher`) and the definition's local
  auxiliaries (`_f`, `_unary`, `_mutual`, `_unsafe_rec`, `match_n`) regardless of namespace prefix, then beta-reduces,
  then erases mdata/binder names. Fixture: a verbatim `evalBinOp` copy inside a namespace in a file that IMPORTS
  `LeanNative.Semantics.Eval` (so Lean reuses `evalBinOp.match_*`) must fail.
- Forbidden set = `LeanNative.Semantics.eval*` and ALL their auxiliary/matcher constants (`eval*.*`), not only private.
- Ratchet = strict set inclusion current ⊆ base (by violation identity); any PR whose allowlist file is not a subset of
  the base allowlist fails.
- "verified" in the assurance table is disallowed if any constant reachable from the cited theorem's statement has an
  entry in the shadow allowlist. Each elevated label needs a recorded quorum review of the theorem statement.
- The initial allowlist is accompanied by an independently produced inventory of target-side declarations (grep/AST
  listing by a second script) to show the checker's coverage; discrepancies must be explained.
