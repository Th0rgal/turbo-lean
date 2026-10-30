#!/usr/bin/env python3
"""B-3 emitter mutation runner (Track B0, spec v4 + [Q3]).

Runs in a disposable git worktree seeded from the local build cache so the
primary checkout is never mutated. Inside every baseline/mutant run, all
default Lake target binaries (`lean-native`, `lean-native-core`,
`turbo-lean-native`, `turbo-zygote`) and `target/release/turbo-lean` are
deleted before rebuilding so stale binaries are impossible by construction,
then rebuilt and SHA-256 hashed before running C3..C7.

After baseline C1, a snapshot of `lean/.lake/build` is kept and restored
before each mutant so `ci-verify`'s `.olean` writes cannot force a 157-job
Lake rebuild. `TURBO_LEAN_HOME` is shared inside the disposable parent dir.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = Path(__file__).resolve().parent / "emitter_mutants.json"
CHECK_ORDER = ("C1", "C2", "C3", "C4", "C5", "C6", "C7")
BACKENDS = ("llvm", "mlir", "ptx", "metal", "c-abi")
LOG_TAIL = 4000
BIN_ARTIFACTS = (
    "lean/.lake/build/bin/lean-native",
    "lean/.lake/build/bin/lean-native-core",
    "lean/.lake/build/bin/turbo-lean-native",
    "lean/.lake/build/bin/turbo-zygote",
    "target/release/turbo-lean",
)
LAKE_DEFAULT_TARGETS = (
    "lean/.lake/build/lib/lean/LeanNative.olean",
    "lean/.lake/build/lib/lean/LeanNative/Core.olean",
    "lean/.lake/build/lib/lean/TurboLean/Spec.olean",
    "lean/.lake/build/lib/lean/TurboLean/Orchestrator.olean",
    "lean/.lake/build/lib/lean/TurboLean/ZygoteWorker.olean",
    "lean/.lake/build/bin/lean-native",
    "lean/.lake/build/bin/lean-native-core",
    "lean/.lake/build/bin/turbo-lean-native",
    "lean/.lake/build/bin/turbo-zygote",
)
ALL_HASH_PATHS = (*LAKE_DEFAULT_TARGETS, "target/release/turbo-lean")


def load_spec() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


def git(argv: list[str], cwd: Path, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *argv], cwd=cwd, check=check, capture_output=True, text=True)


def sha256_file(path: Path) -> str | None:
    if not path.is_file():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def hash_builds(root: Path) -> dict[str, str | None]:
    return {relative: sha256_file(root / relative) for relative in ALL_HASH_PATHS}


def purge_built_executables(root: Path) -> None:
    """Remove every executable artifact so a check can never run a stale binary."""
    for relative in BIN_ARTIFACTS:
        path = root / relative
        if path.is_file() or path.is_symlink():
            path.unlink()


def toolchain(root: Path, env: dict[str, str]) -> dict:
    def version(argv: list[str]) -> str:
        try:
            result = subprocess.run(argv, cwd=root, env=env, capture_output=True, text=True, timeout=30)
        except (OSError, subprocess.TimeoutExpired) as error:
            return str(error)
        lines = ((result.stdout or result.stderr).strip()).splitlines()
        return lines[0] if lines else f"exit {result.returncode}"

    return {
        "lean_toolchain": (root / "lean/lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean": version(["lean", "--version"]),
        "lake": version(["lake", "--version"]),
        "rustc": version(["rustc", "--version"]),
        "cargo": version(["cargo", "--version"]),
        "clang": version(["clang", "--version"]),
        "commit": git(["rev-parse", "HEAD"], root).stdout.strip(),
    }


def prepare_env(root: Path, turbo_home: Path) -> dict[str, str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "4"
    env["PYTHONNOUSERSITE"] = "1"
    env["PYTHONUNBUFFERED"] = "1"
    env["CARGO_TERM_COLOR"] = "never"
    env["CARGO_TARGET_DIR"] = str(root / "target")
    turbo_home.mkdir(parents=True, exist_ok=True)
    env["TURBO_LEAN_HOME"] = str(turbo_home)
    prefix = [
        str(root / "lean/.lake/build/bin"),
        str(root / "target/release"),
        str(Path.home() / ".elan/bin"),
        "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin",
        "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin",
        str(Path.home() / ".cargo/bin"),
    ]
    env["PATH"] = os.pathsep.join([*prefix, env.get("PATH", "")])
    return env


def run_command(argv: list[str], cwd: Path, env: dict[str, str], log_path: Path) -> dict:
    started = time.monotonic()
    try:
        result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
        exit_code = result.returncode
        text = (result.stdout or "") + (result.stderr or "")
    except OSError as error:
        exit_code, text = 127, str(error)
    wall_s = round(time.monotonic() - started, 3)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(text, encoding="utf-8", errors="replace")
    return {
        "exit": exit_code,
        "wall_s": wall_s,
        "log_tail": text[-LOG_TAIL:],
        "log": str(log_path),
    }


def matched_signature(text: str, signatures: list[str]) -> str | None:
    folded = text.lower()
    return next((signature for signature in signatures if signature.lower() in folded), None)


def classify(checks: dict, signatures: list[str], order: tuple[str, ...] = CHECK_ORDER) -> tuple[str, list[str], list[str]]:
    killed, infra = [], []
    for name in order:
        if name not in checks or checks[name]["exit"] == 0:
            continue
        signature = matched_signature(checks[name]["log_tail"], signatures)
        if signature:
            checks[name]["infra_signature"] = signature
            infra.append(name)
        else:
            killed.append(name)
    if killed:
        return "KILLED", killed, infra
    if infra:
        return "INFRA_FAILED", [], infra
    return "SURVIVED", [], []


def c5_flag_check(root: Path, env: dict[str, str]) -> dict:
    argv = ["python3", "scripts/run_conformance_suite.py", "--tier", "C1"]
    result = subprocess.run(argv, cwd=root, env=env, capture_output=True, text=True)
    text = (result.stderr or "") + (result.stdout or "")
    return {
        "argv": argv,
        "exit": result.returncode,
        "unrecognized": result.returncode == 2 and "unrecognized arguments" in text,
        "stderr_tail": text[-500:],
        "used_by_C5": False,
        "note": "C5 runs scripts/run_conformance_suite.py with its default 50 fuzz seeds and no --tier.",
    }


def seed_worktree(worktree: Path) -> None:
    src_lake = ROOT / "lean/.lake"
    if src_lake.is_dir():
        shutil.copytree(src_lake, worktree / "lean/.lake", symlinks=True)
    src_target = ROOT / "target"
    dest_target = worktree / "target"
    if src_target.is_dir() and not dest_target.exists():
        cp_res = subprocess.run(
            ["cp", "-al", str(src_target), str(dest_target)],
            check=False,
            capture_output=True,
        )
        if cp_res.returncode != 0:
            shutil.copytree(src_target, dest_target, symlinks=True)
    purge_built_executables(worktree)


def snapshot_lake_build(root: Path, snapshot: Path) -> None:
    src = root / "lean/.lake/build"
    if snapshot.exists():
        shutil.rmtree(snapshot)
    shutil.copytree(src, snapshot, symlinks=True)


def restore_lake_build(root: Path, snapshot: Path) -> None:
    dest = root / "lean/.lake/build"
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(snapshot, dest, symlinks=True)


def make_worktree(parent: Path, name: str) -> Path:
    path = parent / name
    git(["worktree", "add", "--detach", str(path), "HEAD"], ROOT)
    seed_worktree(path)
    return path


def remove_worktree(path: Path) -> None:
    git(["worktree", "remove", "--force", str(path)], ROOT, check=False)
    shutil.rmtree(path, ignore_errors=True)


def apply_patch(root: Path, mutation: dict) -> tuple[int, str]:
    path = root / mutation["file"]
    text = path.read_text(encoding="utf-8")
    count = text.count(mutation["search"])
    if count != mutation["expected_match_count"]:
        return count, ""
    patched = text.replace(mutation["search"], mutation["replace"], count)
    path.write_text(patched, encoding="utf-8")
    diff = git(["diff", "--", mutation["file"]], root).stdout
    return count, diff


def revert_worktree(root: Path) -> None:
    git(["checkout", "--", "."], root)
    git(["clean", "-fd", "--", "lean"], root, check=False)


def run_pinned_checks(
    root: Path,
    env: dict[str, str],
    spec: dict,
    log_dir: Path,
    check_subset: tuple[str, ...] = CHECK_ORDER,
    lake_snapshot: Path | None = None,
) -> tuple[dict, dict, dict]:
    """Purge built binaries, rebuild all artifacts inside this run, hash them, then run checks."""
    if lake_snapshot is not None and lake_snapshot.is_dir():
        restore_lake_build(root, lake_snapshot)
    purge_built_executables(root)
    pre_purge_hashes = hash_builds(root)
    assert all(pre_purge_hashes[b] is None for b in BIN_ARTIFACTS), pre_purge_hashes

    needs_downstream = any(c not in ("C1", "C2") for c in check_subset)
    ordered: list[str] = []
    if "C1" in check_subset or needs_downstream:
        ordered.append("C1")
    if "C2" in check_subset or needs_downstream:
        ordered.append("C2")
    for name in check_subset:
        if name not in ordered:
            ordered.append(name)

    reports: dict[str, dict] = {}
    post_rebuild_hashes: dict[str, str | None] = {}
    for name in ordered:
        spec_entry = spec["checks"][name]
        before_hashes = hash_builds(root)
        report = run_command(spec_entry["argv"], root, env, log_dir / f"{name}.log")
        after_hashes = hash_builds(root)
        deps = spec_entry["depends_on"]
        report["depends_on"] = deps
        report["artifact_hashes"] = {dep: after_hashes.get(dep) for dep in deps}
        report["changed_during_check"] = sorted(
            path for path, digest in after_hashes.items() if digest != before_hashes.get(path)
        )
        reports[name] = report
        if name == "C2":
            post_rebuild_hashes = after_hashes

    final_hashes = hash_builds(root)
    if not post_rebuild_hashes:
        post_rebuild_hashes = final_hashes

    filtered = {name: reports[name] for name in check_subset}
    rebuild_meta = {
        "purged_binaries_before_run": list(BIN_ARTIFACTS),
        "post_rebuild_hashes": post_rebuild_hashes,
        "final_hashes": final_hashes,
        "all_default_targets_built": all(final_hashes.get(p) is not None for p in ALL_HASH_PATHS),
        "lake_snapshot_restored": lake_snapshot is not None and lake_snapshot.is_dir(),
    }
    return filtered, final_hashes, rebuild_meta


def not_applicable_record(root: Path, mutation: dict) -> dict:
    probe_argv = ["grep", "-n", "-E", "emitRustScalarExpr|emitCScalarExpr|wrapping_sub|emitCAbiBody", "lean/"]
    probe = git(probe_argv, root, check=False)
    commit_check = git(["cat-file", "-t", mutation["not_applicable"]["removed_in"]], root, check=False)
    zero_matches = probe.returncode == 1 and not probe.stdout.strip()
    commit_present = commit_check.returncode == 0 and commit_check.stdout.strip() == "commit"
    evidence = "ZERO_MATCHES" if zero_matches else probe.stdout.strip()
    detail = dict(mutation["not_applicable"])
    detail.update({
        "evidence": evidence,
        "evidence_exit": probe.returncode,
        "removed_in_verified": commit_present,
    })
    return {
        "id": mutation["id"],
        "backend": mutation["backend"],
        "file": mutation["file"],
        "search": mutation["search"],
        "replace": mutation["replace"],
        "expected_match_count": mutation["expected_match_count"],
        "match_count": 0,
        "diff": "",
        "build_hashes": {},
        "checks": {},
        "outcome": "NOT_APPLICABLE" if (zero_matches and commit_present) else "INFRA_FAILED",
        "killed_by": [],
        "not_applicable": detail,
    }


def evaluate_mutation(
    root: Path,
    mutation: dict,
    spec: dict,
    env: dict[str, str],
    log_dir: Path,
    baseline_hashes: dict[str, str | None],
    lake_snapshot: Path | None = None,
) -> dict:
    if mutation.get("not_applicable"):
        return not_applicable_record(root, mutation)

    revert_worktree(root)
    count, diff = apply_patch(root, mutation)
    record = {
        "id": mutation["id"],
        "backend": mutation["backend"],
        "file": mutation["file"],
        "search": mutation["search"],
        "replace": mutation["replace"],
        "expected_match_count": mutation["expected_match_count"],
        "match_count": count,
        "diff": diff,
    }
    if count != mutation["expected_match_count"]:
        record.update({
            "build_hashes": {},
            "checks": {},
            "outcome": "APPLY_FAILED",
            "killed_by": [],
        })
        return record

    try:
        checks, hashes, rebuild_meta = run_pinned_checks(
            root, env, spec, log_dir, lake_snapshot=lake_snapshot
        )
    finally:
        revert_worktree(root)

    outcome, killers, infra_checks = classify(checks, spec["infra_signatures"])
    if checks["C1"]["exit"] == 0 and checks["C2"]["exit"] == 0 and not rebuild_meta["all_default_targets_built"]:
        outcome = "INFRA_FAILED"
        killers = []
        infra_checks = ["missing_default_target_artifact"]

    changed_from_baseline = sorted(
        path for path, digest in hashes.items() if digest is not None and digest != baseline_hashes.get(path)
    )
    record.update({
        "build_hashes": hashes,
        "rebuild": rebuild_meta,
        "changed_from_baseline": changed_from_baseline,
        "checks": checks,
        "outcome": outcome,
        "killed_by": killers,
    })
    if infra_checks:
        record["infra_failed_checks"] = infra_checks
    return record


def summarize(rows: list[dict], spec: dict, expected_universe: list[str]) -> dict:
    counts: dict[str, int] = {}
    by_id = {row["id"]: row for row in rows}
    for row in rows:
        counts[row["outcome"]] = counts.get(row["outcome"], 0) + 1

    decisive = counts.get("KILLED", 0) + counts.get("SURVIVED", 0)
    not_applicable_ids = [row["id"] for row in rows if row["outcome"] == "NOT_APPLICABLE"]
    apply_failed_ids = [row["id"] for row in rows if row["outcome"] == "APPLY_FAILED"]
    infra_failed_ids = [row["id"] for row in rows if row["outcome"] == "INFRA_FAILED"]
    missing_universe_ids = [mid for mid in expected_universe if mid not in by_id]

    rates = {}
    for backend in BACKENDS:
        all_backend = [row for row in rows if row["backend"] == backend]
        selected = [row for row in all_backend if row["outcome"] in {"KILLED", "SURVIVED"}]
        killed = sum(row["outcome"] == "KILLED" for row in selected)
        na_count = sum(row["outcome"] == "NOT_APPLICABLE" for row in all_backend)
        rates[backend] = {
            "killed": killed,
            "survived": len(selected) - killed,
            "decisive": len(selected),
            "not_applicable": na_count,
            "kill_rate": None if not selected else round(killed / len(selected), 6),
        }

    min_decisive = spec["conclusive_minimum"] if len(expected_universe) == len(spec["comparison_universe"]) else (
        len(expected_universe) - len(not_applicable_ids)
    )
    conclusive = (
        decisive >= min_decisive
        and not apply_failed_ids
        and not infra_failed_ids
        and not missing_universe_ids
        and (decisive + len(not_applicable_ids) == len(expected_universe))
    )
    return {
        "counts": counts,
        "decisive": decisive,
        "not_applicable_ids": not_applicable_ids,
        "apply_failed_ids": apply_failed_ids,
        "infra_failed_ids": infra_failed_ids,
        "missing_universe_ids": missing_universe_ids,
        "conclusive": conclusive,
        "kill_rate_per_backend": rates,
    }


def run_suite(output: Path, logs: Path, only_ids: list[str] | None = None) -> dict:
    spec = load_spec()
    if logs.exists():
        shutil.rmtree(logs)
    logs.mkdir(parents=True, exist_ok=True)
    parent = Path(tempfile.mkdtemp(prefix="emitter-mutants-", dir=str(ROOT.parent)))
    commit_sha = git(["rev-parse", "HEAD"], ROOT).stdout.strip()
    expected_universe = list(only_ids) if only_ids is not None else list(spec["comparison_universe"])

    report: dict = {
        "schema": spec["schema"],
        "spec": spec["spec"],
        "commit": commit_sha,
        "comparison_universe": spec["comparison_universe"],
        "evaluated_universe": expected_universe,
        "mutations": [],
    }
    snapshot_seed = ROOT / "lean/.lake/build"
    try:
        work = make_worktree(parent, "work")
        env = prepare_env(work, parent / "turbo-cache")
        report["toolchain"] = toolchain(work, env)
        report["c5_flag_check"] = c5_flag_check(work, env)

        snapshot = parent / "seed_lake_build"
        if snapshot_seed.is_dir():
            shutil.copytree(snapshot_seed, snapshot, symlinks=True)

        baseline_checks, baseline_hashes, baseline_rebuild = run_pinned_checks(work, env, spec, logs / "baseline")
        if not snapshot.is_dir():
            snapshot_lake_build(work, snapshot)
        base_outcome, base_killed, base_infra = classify(baseline_checks, spec["infra_signatures"])
        baseline_passed = base_outcome == "SURVIVED" and baseline_rebuild["all_default_targets_built"]
        failed_baseline = base_killed + base_infra
        if not baseline_rebuild["all_default_targets_built"]:
            failed_baseline.append("missing_default_target_artifact")

        report["build_hashes"] = baseline_hashes
        report["baseline"] = {
            "outcome": "PASSED" if baseline_passed else "INFRA_FAILED",
            "checks": baseline_checks,
            "build_hashes": baseline_hashes,
            "rebuild": baseline_rebuild,
            "failed_checks": failed_baseline,
        }

        if not baseline_passed:
            report["run_outcome"] = "INFRA_FAILED"
            report["kill_rate_per_backend"] = {}
            report["summary"] = {
                "conclusive": False,
                "reason": "baseline pinned check failed; whole run marked INFRA_FAILED per spec",
                "failed_checks": failed_baseline,
            }
        else:
            selected_mutations = [
                m for m in spec["mutations"] if only_ids is None or m["id"] in expected_universe
            ]
            for mutation in selected_mutations:
                rec = evaluate_mutation(
                    work, mutation, spec, env, logs / mutation["id"], baseline_hashes, lake_snapshot=snapshot
                )
                report["mutations"].append(rec)
            summary = summarize(report["mutations"], spec, expected_universe)
            report["summary"] = summary
            report["kill_rate_per_backend"] = summary["kill_rate_per_backend"]
            report["run_outcome"] = "CONCLUSIVE" if summary["conclusive"] else "INCONCLUSIVE"
        remove_worktree(work)
    finally:
        git(["worktree", "prune"], ROOT, check=False)
        shutil.rmtree(parent, ignore_errors=True)

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def run_fixtures(logs: Path, full_checks: bool = False) -> dict:
    """Run all 4 mechanical self-test fixtures from spec v4 against the real emitter.

    With --full-fixtures (used in CI), F2/F4 run full C1..C7; locally without
    --full-fixtures, F2/F4 omit C3 (which has an unrelated 50ms wall-clock
    python plugin budget test that flakes under heavy shared-host CPU load) and
    C4 (covered by the CI suite) while still running C1, C2, C5, C6, C7.
    """
    spec = load_spec()
    fixture_logs = logs / "fixtures"
    if fixture_logs.exists():
        shutil.rmtree(fixture_logs)
    fixture_logs.mkdir(parents=True, exist_ok=True)

    parent = Path(tempfile.mkdtemp(prefix="emitter-mutant-fixtures-", dir=str(ROOT.parent)))
    results: dict[str, dict] = {}
    try:
        work = make_worktree(parent, "work")
        env = prepare_env(work, parent / "turbo-cache")

        base_checks, base_hashes, base_rebuild = run_pinned_checks(
            work, env, spec, fixture_logs / "baseline", check_subset=("C1", "C2")
        )
        snapshot = parent / "seed_lake_build"
        snapshot_lake_build(work, snapshot)
        baseline_ok = (
            base_checks["C1"]["exit"] == 0
            and base_checks["C2"]["exit"] == 0
            and base_rebuild["all_default_targets_built"]
        )

        comment_subset = CHECK_ORDER if full_checks else ("C1", "C2", "C5", "C6", "C7")
        c5_runtime_subset = CHECK_ORDER if full_checks else ("C1", "C2", "C5", "C6", "C7")

        fixtures = [
            (
                "build_breaking",
                {
                    "id": "F1_build_breaking",
                    "backend": "llvm",
                    "file": "lean/LeanNative/Backend/LLVM.lean",
                    "search": "| .sub    => emitLine s!\"  {res} = sub {tyStr} {lVal}, {rVal}\"; return res",
                    "replace": "| .sub    => emitLine (__B0_FIXTURE_BUILD_BREAK__); return res",
                    "expected_match_count": 1,
                },
                ("C1",),
                "KILLED",
            ),
            (
                "comment_only",
                {
                    "id": "F2_comment_only",
                    "backend": "llvm",
                    "file": "lean/LeanNative/Backend/LLVM.lean",
                    "search": "| .sub    => emitLine s!\"  {res} = sub {tyStr} {lVal}, {rVal}\"; return res",
                    "replace": "| .sub    => emitLine s!\"  {res} = sub {tyStr} {lVal}, {rVal}\"; return res -- B0 comment-only fixture",
                    "expected_match_count": 1,
                },
                comment_subset,
                "SURVIVED",
            ),
            (
                "non_matching",
                {
                    "id": "F3_non_matching",
                    "backend": "llvm",
                    "file": "lean/LeanNative/Backend/LLVM.lean",
                    "search": "__B0_NON_EXISTENT_SEARCH_STRING_DOES_NOT_MATCH__",
                    "replace": "unreachable",
                    "expected_match_count": 1,
                },
                ("C1",),
                "APPLY_FAILED",
            ),
            (
                "runtime_only_c5",
                {
                    "id": "F4_runtime_only_c5",
                    "backend": "llvm",
                    "file": "lean/LeanNative/Backend/LLVM.lean",
                    "search": "| .shl    => emitShift \"shl\" \"sh\"\n    | .shr    => emitShift \"lshr\" \"sh\"",
                    "replace": "| .shl    => emitShift \"lshr\" \"sh\"\n    | .shr    => emitShift \"shl\" \"sh\"",
                    "expected_match_count": 1,
                },
                c5_runtime_subset,
                "KILLED",
            ),
        ]

        for name, mutation, subset, expected in fixtures:
            revert_worktree(work)
            count, diff = apply_patch(work, mutation)
            if count != mutation["expected_match_count"]:
                outcome = "APPLY_FAILED"
                killed_by: list[str] = []
                checks: dict = {}
                hashes: dict[str, str | None] = {}
            else:
                try:
                    checks, hashes, _ = run_pinned_checks(
                        work, env, spec, fixture_logs / name, check_subset=subset, lake_snapshot=snapshot
                    )
                finally:
                    revert_worktree(work)
                outcome, killed_by, _ = classify(checks, spec["infra_signatures"], order=subset)

            passed = baseline_ok and outcome == expected
            extra: dict = {}
            if name == "build_breaking":
                passed = passed and "C1" in killed_by
            elif name == "comment_only":
                passed = passed and killed_by == []
            elif name == "non_matching":
                passed = passed and count == 0
            elif name == "runtime_only_c5":
                compiled_cleanly = checks.get("C1", {}).get("exit") == 0 and checks.get("C2", {}).get("exit") == 0
                non_c5_clean = all(
                    checks.get(cname, {}).get("exit") == 0 for cname in subset if cname != "C5"
                )
                core_rebuilt = (
                    hashes.get("lean/.lake/build/bin/lean-native-core") is not None
                    and hashes.get("lean/.lake/build/bin/lean-native-core")
                    != base_hashes.get("lean/.lake/build/bin/lean-native-core")
                )
                killed_by_c5 = killed_by == ["C5"]
                passed = passed and compiled_cleanly and non_c5_clean and core_rebuilt and killed_by_c5
                extra = {
                    "compiled_cleanly": compiled_cleanly,
                    "non_c5_checks_clean": non_c5_clean,
                    "lean_native_core_hash_changed_from_baseline": core_rebuilt,
                    "baseline_lean_native_core_sha256": base_hashes.get("lean/.lake/build/bin/lean-native-core"),
                    "mutant_lean_native_core_sha256": hashes.get("lean/.lake/build/bin/lean-native-core"),
                }

            results[name] = {
                "id": mutation["id"],
                "expected": expected,
                "outcome": outcome,
                "killed_by": killed_by,
                "match_count": count,
                "diff_nonempty": bool(diff),
                "passed": passed,
                **extra,
            }
        remove_worktree(work)
    finally:
        git(["worktree", "prune"], ROOT, check=False)
        shutil.rmtree(parent, ignore_errors=True)

    return {
        "schema": "emitter-mutants-fixtures-v1",
        "baseline_compile_ok": baseline_ok,
        "passed": all(item["passed"] for item in results.values()),
        "fixtures": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", action="store_true", help="run the 4 required self-test fixtures")
    parser.add_argument("--full-fixtures", action="store_true", help="include C3/C4 in F2/F4 fixtures (for CI)")
    parser.add_argument("--fixtures-output", type=Path, help="optional path to write fixture JSON report")
    parser.add_argument("--only", help="comma-separated subset of mutation IDs for targeted testing")
    parser.add_argument("--output", type=Path, default=ROOT / "emitter-mutation-report.json")
    parser.add_argument("--logs", type=Path, default=ROOT / "emitter-mutation-logs")
    args = parser.parse_args()

    if args.fixtures:
        report = run_fixtures(args.logs, full_checks=args.full_fixtures)
        text = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.fixtures_output:
            args.fixtures_output.parent.mkdir(parents=True, exist_ok=True)
            args.fixtures_output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 0 if report["passed"] else 1

    only_ids = [item.strip() for item in args.only.split(",") if item.strip()] if args.only else None
    report = run_suite(args.output, args.logs, only_ids=only_ids)
    print(
        json.dumps(
            {
                "output": str(args.output),
                "run_outcome": report["run_outcome"],
                "summary": report.get("summary", {}),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["run_outcome"] == "CONCLUSIVE" else 1


if __name__ == "__main__":
    raise SystemExit(main())
