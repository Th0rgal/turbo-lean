#!/usr/bin/env python3
"""W2-H1.4 H1 mutant kill matrix and coverage-ratchet gate (`scripts/h1_mutant_matrix.py`).

Work-graph leaf **H1.4** (`roadmap/HORIZONS.md`): mutant kill matrix in CI, coverage number
published. The gate fails closed (exit 1) unless all of the following hold:

1. `lean/LeanNative/Proofs/H1/SpecLocked.lean` hashes to `SPEC_LOCKED_SHA256` (the `H1.F` pin).
2. Every theorem in `H1_KILLED_MUTANTS` is declared in its source file as a negated statement
   (`theorem <name> : ¬ ...`), and at least `MIN_KILLED_MUTANTS` of them exist.
3. The kernel axiom audit (`lean-native-core audit-axioms --json`) passed, audited at least
   `AUDITED_THEOREM_FLOOR` theorems, found no forbidden axiom, and lists every mutant theorem as
   present in the environment, passing, and using only `STANDARD_AXIOMS` (so no `sorryAx` and no
   `Lean.trustCompiler`).
4. With `--with-coverage-ratchet`, `python3 scripts/lcnf_coverage.py --check` exits 0; that check
   enforces the H1 coverage ratchet (`H1_COVERAGE_RATCHET` in `lcnf_coverage.py`) and that the
   committed `benchmarks/h1_coverage_ratchet.json` matches the live measurement.

The audit JSON comes from `--audit-json PATH` (`-` for stdin) or from running `--core-bin`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent

SPEC_LOCKED_PATH = "lean/LeanNative/Proofs/H1/SpecLocked.lean"
SPEC_LOCKED_SHA256 = "1139c286dd53ddd9aa63f599f24c6d286836f88e2c2f27fa96d5ce4ec7a93970"

AUDITED_THEOREM_FLOOR = 904
MIN_KILLED_MUTANTS = 10
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
H1_NAMESPACE = "LeanNative.Proofs.H1"

# (theorem short name, declaring file, rung, what the mutant breaks). Each theorem states
# `¬ <H1 refinement> (mutate <mutant>)`: the mutated lowerer is refuted by the locked statement.
H1_KILLED_MUTANTS: tuple[tuple[str, str, str, str], ...] = (
    ("negWitnessInvertedBranch_killed", "lean/LeanNative/Proofs/H1/SpecLocked.lean", "H1.F", "branch arms swapped"),
    ("negWitnessWrongReturn_killed", "lean/LeanNative/Proofs/H1/SpecLocked.lean", "H1.F", "wrong returned variable"),
    ("negWitnessDroppedParam_killed", "lean/LeanNative/Proofs/H1/SpecLocked.lean", "H1.F", "parameter dropped"),
    ("negWitnessWrongScrutinee_killed", "lean/LeanNative/Proofs/H1/SpecLocked.lean", "H1.F", "wrong case scrutinee"),
    ("negWitnessSwappedArith_killed", "lean/LeanNative/Proofs/H1/LowerSound.lean", "L1", "arithmetic operands swapped"),
    ("negWitnessWrongCallTarget_killed", "lean/LeanNative/Proofs/H1/FirstOrderCalls.lean", "L2", "call to the wrong callee"),
    ("negWitnessSwappedCallArgs_killed", "lean/LeanNative/Proofs/H1/FirstOrderCalls.lean", "L2", "call arguments swapped"),
    ("negWitnessBrokenRecStep_killed", "lean/LeanNative/Proofs/H1/RecursionAndJoinPoints.lean", "L3", "broken recursive step"),
    ("negWitnessSwappedMutualTargets_killed", "lean/LeanNative/Proofs/H1/RecursionAndJoinPoints.lean", "L3", "mutual call targets swapped"),
    ("negWitnessWrongJoinArg_killed", "lean/LeanNative/Proofs/H1/RecursionAndJoinPoints.lean", "L3", "wrong join-point argument"),
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_spec_lock(root: Path) -> list[str]:
    path = root / SPEC_LOCKED_PATH
    if not path.is_file():
        return [f"Missing locked H1 statement: {SPEC_LOCKED_PATH}"]
    actual = sha256_file(path)
    if actual != SPEC_LOCKED_SHA256:
        return [f"{SPEC_LOCKED_PATH} drifted: pinned sha256={SPEC_LOCKED_SHA256} actual={actual}"]
    return []


def check_mutant_sources(root: Path, mutants=H1_KILLED_MUTANTS) -> list[str]:
    errors: list[str] = []
    if len({m[0] for m in mutants}) < MIN_KILLED_MUTANTS:
        errors.append(f"Mutant kill matrix has {len({m[0] for m in mutants})} distinct mutants, floor is {MIN_KILLED_MUTANTS}")
    for name, rel, _rung, _what in mutants:
        path = root / rel
        if not path.is_file():
            errors.append(f"Mutant `{name}`: declaring file {rel} is missing")
            continue
        decl = re.compile(rf"^theorem\s+{re.escape(name)}\s*:\s*¬", re.MULTILINE)
        if not decl.search(path.read_text(encoding="utf-8")):
            errors.append(f"Mutant `{name}` is not declared as `theorem {name} : ¬ ...` in {rel}")
    return errors


def check_axiom_audit(doc: Any, mutants=H1_KILLED_MUTANTS) -> list[str]:
    if not isinstance(doc, dict):
        return [f"Axiom audit output must be a JSON object, got {type(doc).__name__}"]
    errors: list[str] = []
    if doc.get("passed") is not True:
        errors.append(f"Axiom audit did not pass: passed={doc.get('passed')!r}")
    audited = doc.get("theoremsAudited")
    if isinstance(audited, bool) or not isinstance(audited, int) or audited < AUDITED_THEOREM_FLOOR:
        errors.append(f"Axiom audit covered {audited!r} theorems, floor is {AUDITED_THEOREM_FLOOR}")
    if doc.get("forbiddenAxiomsFound") != []:
        errors.append(f"Axiom audit found forbidden axioms: {doc.get('forbiddenAxiomsFound')!r}")
    results = doc.get("results")
    if not isinstance(results, list):
        return errors + ["Axiom audit output has no `results` list"]
    by_name = {r.get("theoremName"): r for r in results if isinstance(r, dict)}
    for name, *_ in mutants:
        fq = f"{H1_NAMESPACE}.{name}"
        r = by_name.get(fq)
        if r is None:
            errors.append(f"Mutant `{fq}` is missing from the axiom audit")
            continue
        used = r.get("axiomsUsed")
        nonstandard = sorted(set(used) - STANDARD_AXIOMS) if isinstance(used, list) else used
        if (
            r.get("existsInEnv") is not True
            or r.get("passed") is not True
            or r.get("forbiddenFound") != []
            or r.get("nonStandardFound") != []
            or nonstandard != []
        ):
            errors.append(
                f"Mutant `{fq}` is not kernel-clean: existsInEnv={r.get('existsInEnv')!r} "
                f"passed={r.get('passed')!r} forbiddenFound={r.get('forbiddenFound')!r} "
                f"nonStandardFound={r.get('nonStandardFound')!r} non-standard axiomsUsed={nonstandard!r}"
            )
    return errors


def load_audit(audit_json: str | None, core_bin: str | None) -> tuple[Any, list[str]]:
    try:
        if audit_json == "-":
            return json.load(sys.stdin), []
        if audit_json is not None:
            return json.loads(Path(audit_json).read_text(encoding="utf-8")), []
        if core_bin is None:
            return None, ["Neither --audit-json nor --core-bin was given"]
        res = subprocess.run([core_bin, "audit-axioms", "--json"], capture_output=True, text=True, timeout=590)
        if res.returncode != 0:
            return None, [f"`{core_bin} audit-axioms --json` exited {res.returncode}: {res.stderr.strip()}"]
        return json.loads(res.stdout), []
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        return None, [f"Could not obtain the axiom audit: {exc}"]


def run_coverage_ratchet(root: Path) -> list[str]:
    try:
        res = subprocess.run(
            [sys.executable, str(root / "scripts" / "lcnf_coverage.py"), "--check"],
            cwd=root, capture_output=True, text=True, timeout=590,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return [f"lcnf_coverage.py --check could not run: {exc}"]
    print(res.stdout.strip())
    if res.returncode != 0:
        return [f"lcnf_coverage.py --check exited {res.returncode}: {res.stderr.strip()}"]
    return []


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=ROOT_DIR, help="Repository root to check")
    ap.add_argument("--audit-json", help="Axiom audit JSON file (`-` for stdin)")
    ap.add_argument("--core-bin", help="lean-native-core binary to run `audit-axioms --json` with")
    ap.add_argument("--with-coverage-ratchet", action="store_true", help="Also run `lcnf_coverage.py --check`")
    ap.add_argument("--json", action="store_true", help="Emit the matrix verdict as JSON")
    args = ap.parse_args(argv)
    root = args.root.resolve()

    errors = check_spec_lock(root) + check_mutant_sources(root)
    audit, load_errors = load_audit(args.audit_json, args.core_bin)
    errors += load_errors if load_errors else check_axiom_audit(audit)
    if args.with_coverage_ratchet:
        errors += run_coverage_ratchet(root)

    if args.json:
        print(json.dumps({
            "ok": not errors,
            "errors": errors,
            "spec_locked": {"path": SPEC_LOCKED_PATH, "sha256": SPEC_LOCKED_SHA256},
            "killed_mutants": [f"{H1_NAMESPACE}.{m[0]}" for m in H1_KILLED_MUTANTS],
            "theorems_audited": audit.get("theoremsAudited") if isinstance(audit, dict) else None,
        }, indent=2, sort_keys=True))
    for err in errors:
        print(f"  [ERROR] {err}", file=sys.stderr)
    if errors:
        return 1
    if not args.json:
        print(
            f"  [OK] H1 mutant matrix: {len(H1_KILLED_MUTANTS)} mutants killed in kernel "
            f"(0 sorryAx, 0 trustCompiler), {audit['theoremsAudited']} theorems audited, "
            f"SpecLocked.lean sha256={SPEC_LOCKED_SHA256[:12]}"
            + (", coverage ratchet held" if args.with_coverage_ratchet else "")
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
