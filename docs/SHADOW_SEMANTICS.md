# Shadow-semantics checker (Track B0)

`scripts/check_shadow_semantics.lean` reports every violation identity
`(target declaration, forbidden evaluator, kind)` with `kind ∈ {call≤3, call∞, clone}`, where the
targets are the declarations of the pinned modules and namespaces in
`scripts/shadow_inventory.json`, and the forbidden set is `LeanNative.Semantics.eval*` together with
all of their auxiliaries.

- **call≤3 / call∞**: a forbidden constant is reachable from the target in the dependency graph.
  The graph includes types, values, `.proj`, constructors, recursor rules, matcher, equation,
  `_unsafe_rec` and `_proof_n` auxiliaries, `implemented_by` targets and instances.
- **clone**: some definition in the target's dependency closure, in any module or namespace, has a
  canonical body equal to a forbidden evaluator's. Detection covers verbatim and alpha-equivalent
  copies only. Copies that differ by eta-expansion, `let` changes or reordered match arms are out of
  scope.

Run it from `lean/`:

```
lake build ShadowFixtures
LEAN_NUM_THREADS=4 lake env lean --run ../scripts/check_shadow_semantics.lean --self-test --base <BASE_SHA>
```

The `--self-test` flag runs the fixtures in `lean/ShadowFixtures/`. It also runs the ratchet cases,
which call the real `checkRatchet` against a temporary git repository.

## Ratchet

The violation identities are compared with `scripts/shadow_allowlist.json`:

- The working-tree allowlist must be a subset of the allowlist at `<BASE_SHA>`, so no entry may be
  added.
- The working-tree allowlist must equal the current violation set: no violation may be missing and
  no entry may be stale.
- The inventory must not drop any module, namespace or source root that exists at the base.

Bootstrap applies only when the base commit has neither the checker nor an allowlist. In that case
the base allowlist is taken to be the current violation set. Because of the equality rule, the
introducing allowlist must then list exactly the existing violations; an empty allowlist fails.

## Enforcement

**None of this is enforced today.** The `Th0rgal/turbo-lean` repository has no branch protection
and no rulesets on `main`, and it has no required status checks. As a result:

- A failing shadow-semantics step fails the `Build turbo-lean & Self-Verify Lean 4 Proofs` job, but
  it does not stop a merge.
- `.github/CODEOWNERS` only *requests* a review from `@Th0rgal`. It does not require that review.

For the ratchet to be merge-blocking, a repository admin must configure the following. This PR does
not change any repository settings.

1. **Ruleset on `main`** (Settings → Rules → Rulesets → New branch ruleset): set the target to the
   default branch (`main`), set enforcement to *Active*, and leave the bypass list empty. Admins
   should not be on the bypass list either, or the ruleset can be skipped.
   - **Require status checks to pass**: add the check `Build turbo-lean & Self-Verify Lean 4 Proofs`
     (the `verify` job in `.github/workflows/ci.yml`). Also enable *Require branches to be up to
     date before merging* so the ratchet runs against the actual merge base.
   - **Require a pull request before merging**, with:
     - *Require review from Code Owners* turned on. This makes the CODEOWNERS entries for
       `scripts/shadow_allowlist.json` and `scripts/shadow_inventory.json` binding, together with
       the checker, the fixtures, `.github/CODEOWNERS` and `.github/workflows/ci.yml`.
     - *Dismiss stale pull request approvals when new commits are pushed* turned on.
     - Required approvals set to at least 1.
   - **Block force pushes** and **Restrict deletions** on `main`.
   - The equivalent classic setting is Settings → Branches → branch protection rule for `main`, with
     the same options checked.
2. **Sole-owner caveat**: GitHub does not let a pull request's author approve their own pull
   request. `@Th0rgal` is the only code owner, so with *Require review from Code Owners* turned on,
   a PR authored by `@Th0rgal` that touches `scripts/shadow_allowlist.json` or
   `scripts/shadow_inventory.json` cannot get the required approval. It can only merge through a
   ruleset bypass, which defeats the control. The fix is to add a second code owner, for example a
   team or a trusted reviewer account, to those two lines in `.github/CODEOWNERS`. Alternatively,
   accept that changes by the sole owner are not independently reviewed.
3. **Verification after setup**: run
   `gh api repos/Th0rgal/turbo-lean/rulesets` (or
   `gh api repos/Th0rgal/turbo-lean/branches/main/protection`). The output should list the required
   check and `require_code_owner_review: true`. Then open a test PR that adds an allowlist entry and
   confirm that the merge button is blocked.
