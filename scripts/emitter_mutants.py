#!/usr/bin/env python3
"""B-3 emitter mutation runner (Track B0, spec v4 + [Q3]).

Runs in a disposable git worktree seeded from the local build cache so the
primary checkout is never mutated. Inside every baseline/mutant run, all
default Lake target binaries (`lean-native`, `lean-native-core`,
`turbo-lean-native`, `turbo-zygote`) and `target/release/turbo-lean` are
purged and re-linked after Lake's incremental module build. All default
targets, the Rust executable, and the mutated emitter modules' own .oleans
are SHA-256 hashed before running C3..C7. A failed C1/C2 skips subsequent
checks; infrastructure signatures in the full output or signal termination
override all kills.

Durable atomic report checkpoints: a checkpoint JSON is written next to the
report before work starts and flushed after every check/case (baseline,
fixtures, mutants). Completed steps keep their exit codes, timings and
provenance; active and pending steps remain explicitly INCOMPLETE after an
abrupt death and are never turned into SURVIVED/KILLED/PASSED/CONCLUSIVE.

The non-blocking mutation CI job runs on push/workflow_dispatch, not PRs.
C5 uses the default 50 fuzz seeds without --tier (keeping C5 runtime bounded
per mutant), while `c5_flag_check` verifies `--tier` flag parsing and fail-closed
rejection of unknown tiers.

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
COMPARISON_UNIVERSE = tuple(f"M{i}" for i in range(1, 11))
BACKENDS = ("llvm", "mlir", "ptx", "metal")
LOG_TAIL = 4000
CHECKPOINT_SCHEMA = "emitter-mutants-checkpoint-v1"
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
EMITTER_MODULES = tuple(
    f"lean/.lake/build/lib/lean/LeanNative/Backend/{module}.olean"
    for module in ("LLVM", "MLIRGPU", "Metal")
)
ALL_HASH_PATHS = (*LAKE_DEFAULT_TARGETS, *EMITTER_MODULES, "target/release/turbo-lean")


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


def atomic_write_json(path: Path, payload: dict) -> None:
    """Durably write JSON: fsync a temp file, atomically replace, fsync the dir.

    A crash mid-write can never expose a torn file or erase the previous
    evidence at `path`: readers only ever see whole files, and a failed write
    removes its temp file while leaving the old contents intact.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        with tmp.open("w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    except BaseException:
        tmp.unlink(missing_ok=True)
        raise
    dir_fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


def checkpoint_sibling(path: Path) -> Path:
    """Durable checkpoint file living beside a report/output path."""
    return path.with_name(path.name + ".checkpoint.json")


class Checkpoint:
    """Durable per-step journal of a suite/fixtures run (report checkpointing).

    The payload carries the run so far: `steps` maps completed step ids to
    their full evidence (exit codes, timings, logs, provenance), `pending`
    lists every step not yet completed, and `complete` stays False with
    `run_outcome` "INCOMPLETE" until the run finishes normally. An in-flight
    case is marked {"status": "INCOMPLETE", "complete": False} before its work
    starts, so an abrupt death is always explicitly incomplete and can never
    be mistaken for SURVIVED/KILLED/PASSED/CONCLUSIVE.
    """

    def __init__(self, path: Path, payload: dict):
        self.path = path
        self.payload = {**payload, "complete": False, "run_outcome": "INCOMPLETE", "pending": [], "steps": {}}
        self.flush()

    def declare(self, *steps: str) -> None:
        """Checkpoint the planned work before any of it starts."""
        self.payload["pending"] = sorted(set(self.payload["pending"]) | set(steps))
        self.flush()

    def start(self, step: str) -> None:
        """Mark an in-flight case explicitly INCOMPLETE before its work starts."""
        self.note(step, {"started_at": time.time()})

    def note(self, step: str, entry: dict) -> None:
        """Merge evidence into a not-yet-completed (active) step."""
        active = self.payload["steps"].setdefault(step, {"status": "INCOMPLETE", "complete": False})
        for key, value in entry.items():
            if isinstance(value, dict) and isinstance(active.get(key), dict):
                active[key].update(value)
            else:
                active[key] = value
        self.flush()

    def record(self, step: str, entry: dict) -> None:
        """Mark a step completed with its final evidence."""
        self.payload["steps"][step] = entry
        self.payload["pending"] = [name for name in self.payload["pending"] if name != step]
        self.flush()

    def finish(self, run_outcome: str, summary: dict) -> None:
        self.payload["complete"] = run_outcome != "INCOMPLETE"
        self.payload["run_outcome"] = run_outcome
        self.payload["summary"] = summary
        self.flush()

    def flush(self) -> None:
        self.payload["updated_at"] = time.time()
        atomic_write_json(self.path, self.payload)


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
    # Pin elan-shimmed children (lean / lake) to the repo toolchain so a child
    # running outside the repo never resolves elan's default toolchain.
    try:
        toolchain_pin = (root / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError:
        toolchain_pin = ""
    if toolchain_pin:
        env["ELAN_TOOLCHAIN"] = toolchain_pin
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


def run_command(argv: list[str], cwd: Path, env: dict[str, str], log_path: Path, signatures: list[str]) -> dict:
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
        "infra_signature": f"signal:{-exit_code}" if exit_code < 0 else matched_signature(text, signatures),
    }


def matched_signature(text: str, signatures: list[str]) -> str | None:
    folded = text.lower()
    return next((signature for signature in signatures if signature.lower() in folded), None)


def classify(checks: dict, order: tuple[str, ...] = CHECK_ORDER) -> tuple[str, list[str], list[str]]:
    killed, infra = [], []
    prereq_failed = False
    for name in order:
        if name not in checks:
            continue
        check = checks[name]
        signature = check.get("infra_signature")
        if signature:
            infra.append(name)
        elif check.get("status") != "SKIPPED_PREREQ" and check["exit"] != 0 and not prereq_failed:
            killed.append(name)
        if name in ("C1", "C2") and check["exit"] != 0:
            prereq_failed = True
    if infra:
        return "INFRA_FAILED", [], infra
    if killed:
        return "KILLED", killed, []
    return "SURVIVED", [], []


def c5_flag_check(root: Path, env: dict[str, str]) -> dict:
    help_argv = ["python3", "scripts/run_conformance_suite.py", "--help"]
    help_res = subprocess.run(help_argv, cwd=root, env=env, capture_output=True, text=True)
    help_text = (help_res.stdout or "") + (help_res.stderr or "")
    bad_argv = ["python3", "scripts/run_conformance_suite.py", "--tier", "C99"]
    bad_res = subprocess.run(bad_argv, cwd=root, env=env, capture_output=True, text=True)
    bad_text = (bad_res.stderr or "") + (bad_res.stdout or "")
    return {
        "argv": bad_argv,
        "exit": bad_res.returncode,
        "tier_flag_supported": help_res.returncode == 0 and "--tier" in help_text,
        "unknown_tier_rejected": bad_res.returncode == 2 and "Unknown conformance tier" in bad_text,
        "stderr_tail": bad_text[-500:],
        "used_by_C5": False,
        "note": "C5 runs scripts/run_conformance_suite.py with its default 50 fuzz seeds (tier C4); --tier C1,C4 runs in blocking roadmap-conformance CI.",
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


def rmtree_writable(path: Path) -> None:
    if not path.exists():
        return

    def _onerror(func, p, _exc_info):
        try:
            parent_dir = os.path.dirname(p)
            if parent_dir:
                os.chmod(parent_dir, 0o700)
            os.chmod(p, 0o700)
            func(p)
        except OSError:
            pass

    shutil.rmtree(path, onerror=_onerror)


def remove_worktree(path: Path) -> None:
    git(["worktree", "remove", "--force", str(path)], ROOT, check=False)
    rmtree_writable(path)


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


def ordered_checks(check_subset: tuple[str, ...]) -> list[str]:
    """Execution order: C1/C2 prerequisites first, then the subset in order."""
    needs_downstream = any(c not in ("C1", "C2") for c in check_subset)
    ordered: list[str] = []
    if "C1" in check_subset or needs_downstream:
        ordered.append("C1")
    if "C2" in check_subset or needs_downstream:
        ordered.append("C2")
    for name in check_subset:
        if name not in ordered:
            ordered.append(name)
    return ordered


def run_pinned_checks(
    root: Path,
    env: dict[str, str],
    spec: dict,
    log_dir: Path,
    check_subset: tuple[str, ...] = CHECK_ORDER,
    lake_snapshot: Path | None = None,
    on_check=None,
) -> tuple[dict, dict, dict]:
    """Incrementally build modules, re-link purged executables, hash, then check.

    `on_check(name, report)` fires after each completed check so callers can
    checkpoint per-check evidence.
    """
    if lake_snapshot is not None and lake_snapshot.is_dir():
        restore_lake_build(root, lake_snapshot)
    purge_built_executables(root)
    pre_purge_hashes = hash_builds(root)
    assert all(pre_purge_hashes[b] is None for b in BIN_ARTIFACTS), pre_purge_hashes

    reports: dict[str, dict] = {}
    post_rebuild_hashes: dict[str, str | None] = {}
    failed_prereqs: list[str] = []
    for name in ordered_checks(check_subset):
        spec_entry = spec["checks"][name]
        before_hashes = hash_builds(root)
        if failed_prereqs:
            report = {
                "status": "SKIPPED_PREREQ", "exit": None, "wall_s": 0,
                "log_tail": "", "skipped_prerequisites": list(failed_prereqs),
            }
        else:
            report = run_command(spec_entry["argv"], root, env, log_dir / f"{name}.log", spec["infra_signatures"])
            if name in ("C1", "C2") and report["exit"] != 0:
                failed_prereqs.append(name)
        after_hashes = hash_builds(root)
        deps = spec_entry["depends_on"]
        report["depends_on"] = deps
        report["artifact_hashes"] = {dep: after_hashes.get(dep) for dep in deps}
        report["changed_during_check"] = sorted(
            path for path, digest in after_hashes.items() if digest != before_hashes.get(path)
        )
        reports[name] = report
        if on_check is not None:
            on_check(name, report)
        if name == "C2":
            post_rebuild_hashes = after_hashes

    final_hashes = hash_builds(root)
    if not post_rebuild_hashes:
        post_rebuild_hashes = final_hashes

    rebuild_meta = {
        "purged_binaries_before_run": list(BIN_ARTIFACTS),
        "post_rebuild_hashes": post_rebuild_hashes,
        "final_hashes": final_hashes,
        "all_default_targets_built": all(final_hashes.get(p) is not None for p in ALL_HASH_PATHS),
        "lake_snapshot_restored": lake_snapshot is not None and lake_snapshot.is_dir(),
    }
    return reports, final_hashes, rebuild_meta


def evaluate_mutation(
    root: Path,
    mutation: dict,
    spec: dict,
    env: dict[str, str],
    log_dir: Path,
    baseline_hashes: dict[str, str | None],
    lake_snapshot: Path | None = None,
    check_subset: tuple[str, ...] = CHECK_ORDER,
    on_check=None,
) -> dict:
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
            root, env, spec, log_dir, check_subset=check_subset, lake_snapshot=lake_snapshot, on_check=on_check
        )
    finally:
        revert_worktree(root)

    outcome, killers, infra_checks = classify(checks, order=check_subset)
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


def summarize(rows: list[dict], spec: dict, expected_universe: list[str], targeted: bool = False) -> dict:
    counts: dict[str, int] = {}
    by_id = {row["id"]: row for row in rows}
    for row in rows:
        counts[row["outcome"]] = counts.get(row["outcome"], 0) + 1

    decisive = counts.get("KILLED", 0) + counts.get("SURVIVED", 0)
    apply_failed_ids = [row["id"] for row in rows if row["outcome"] == "APPLY_FAILED"]
    infra_failed_ids = [row["id"] for row in rows if row["outcome"] == "INFRA_FAILED" or row.get("infra_failed_checks")]
    missing_universe_ids = [mid for mid in COMPARISON_UNIVERSE if mid not in by_id]
    unexpected_universe_ids = sorted(set(by_id) - set(COMPARISON_UNIVERSE))
    targeted = targeted or set(expected_universe) != set(COMPARISON_UNIVERSE)

    rates = {}
    for backend in BACKENDS:
        all_backend = [row for row in rows if row["backend"] == backend]
        selected = [row for row in all_backend if row["outcome"] in {"KILLED", "SURVIVED"}]
        killed = sum(row["outcome"] == "KILLED" for row in selected)
        rates[backend] = {
            "killed": killed,
            "survived": len(selected) - killed,
            "decisive": len(selected),
            "kill_rate": None if not selected else round(killed / len(selected), 6),
        }

    conclusive = (
        not targeted
        and tuple(spec["comparison_universe"]) == COMPARISON_UNIVERSE
        and decisive >= spec["conclusive_minimum"]
        and not apply_failed_ids
        and not infra_failed_ids
        and not missing_universe_ids
        and not unexpected_universe_ids
        and len(rows) == len(by_id) == len(COMPARISON_UNIVERSE)
        and decisive == len(COMPARISON_UNIVERSE)
    )
    return {
        "counts": counts,
        "decisive": decisive,
        "apply_failed_ids": apply_failed_ids,
        "infra_failed_ids": infra_failed_ids,
        "missing_universe_ids": missing_universe_ids,
        "unexpected_universe_ids": unexpected_universe_ids,
        "conclusive": conclusive,
        "run_outcome": "TARGETED" if targeted else ("CONCLUSIVE" if conclusive else "INCONCLUSIVE"),
        "kill_rate_per_backend": rates,
    }


def run_suite(
    output: Path,
    logs: Path,
    only_ids: list[str] | None = None,
    check_subset: tuple[str, ...] = CHECK_ORDER,
) -> dict:
    spec = load_spec()
    if logs.exists():
        rmtree_writable(logs)
    logs.mkdir(parents=True, exist_ok=True)
    commit_sha = git(["rev-parse", "HEAD"], ROOT).stdout.strip()
    expected_universe = list(only_ids) if only_ids is not None else list(spec["comparison_universe"])
    selected_mutations = [
        m for m in spec["mutations"] if only_ids is None or m["id"] in expected_universe
    ]

    checkpoint = Checkpoint(checkpoint_sibling(output), {
        "schema": CHECKPOINT_SCHEMA,
        "kind": "suite",
        "commit": commit_sha,
        "output": str(output),
        "check_subset": list(check_subset),
        "evaluated_universe": expected_universe,
        "targeted": only_ids is not None,
    })
    checkpoint.declare(
        "provenance",
        *(f"baseline:{name}" for name in ordered_checks(check_subset)),
        *(f"mutant:{mutation['id']}" for mutation in selected_mutations),
    )
    parent = Path(tempfile.mkdtemp(prefix="emitter-mutants-", dir=str(ROOT.parent)))

    report: dict = {
        "schema": spec["schema"],
        "spec": spec["spec"],
        "commit": commit_sha,
        "comparison_universe": spec["comparison_universe"],
        "evaluated_universe": expected_universe,
        "mutations": [],
    }
    snapshot_seed = ROOT / "lean/.lake/build"
    completed = False
    try:
        work = make_worktree(parent, "work")
        env = prepare_env(work, parent / "turbo-cache")
        report["toolchain"] = toolchain(work, env)
        report["c5_flag_check"] = c5_flag_check(work, env)
        checkpoint.record("provenance", {
            "commit": commit_sha,
            "toolchain": report["toolchain"],
            "c5_flag_check": report["c5_flag_check"],
        })

        snapshot = parent / "seed_lake_build"
        if snapshot_seed.is_dir():
            shutil.copytree(snapshot_seed, snapshot, symlinks=True)

        baseline_checks, baseline_hashes, baseline_rebuild = run_pinned_checks(
            work, env, spec, logs / "baseline", check_subset=check_subset,
            on_check=lambda name, check: checkpoint.record(f"baseline:{name}", check),
        )
        base_outcome, base_killed, base_infra = classify(baseline_checks, order=check_subset)
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
        checkpoint.record("baseline:outcome", {
            "outcome": report["baseline"]["outcome"],
            "failed_checks": failed_baseline,
            "build_hashes": baseline_hashes,
        })

        if not baseline_passed:
            report["run_outcome"] = "INFRA_FAILED"
            report["kill_rate_per_backend"] = {}
            report["summary"] = {
                "conclusive": False,
                "reason": "baseline pinned check failed; whole run marked INFRA_FAILED per spec",
                "failed_checks": failed_baseline,
            }
        else:
            if not snapshot.is_dir():
                snapshot_lake_build(work, snapshot)
            for mutation in selected_mutations:
                step = f"mutant:{mutation['id']}"
                checkpoint.start(step)
                checkpoint.note(step, {"id": mutation["id"], "backend": mutation["backend"]})
                rec = evaluate_mutation(
                    work,
                    mutation,
                    spec,
                    env,
                    logs / mutation["id"],
                    baseline_hashes,
                    lake_snapshot=snapshot,
                    check_subset=check_subset,
                    on_check=lambda name, check, step=step: checkpoint.note(step, {"checks": {name: check}}),
                )
                report["mutations"].append(rec)
                checkpoint.record(step, rec)
            summary = summarize(report["mutations"], spec, expected_universe, targeted=only_ids is not None)
            report["summary"] = summary
            report["kill_rate_per_backend"] = summary["kill_rate_per_backend"]
            report["run_outcome"] = summary["run_outcome"]
        completed = True
        remove_worktree(work)
    finally:
        if not completed:
            summary = dict(report.get("summary") or {})
            summary.update({
                "conclusive": False,
                "run_outcome": "INCOMPLETE",
                "reason": "run interrupted before completion; completed evidence and pending steps are in the checkpoint",
                "pending": list(checkpoint.payload["pending"]),
            })
            report["run_outcome"] = "INCOMPLETE"
            report["summary"] = summary
            report["kill_rate_per_backend"] = report.get("kill_rate_per_backend", {})
        checkpoint.finish(report["run_outcome"], report["summary"])
        atomic_write_json(output, report)
        git(["worktree", "prune"], ROOT, check=False)
        rmtree_writable(parent)
    return report


def run_fixtures(logs: Path, full_checks: bool = False, checkpoint_path: Path | None = None) -> dict:
    """Run all 4 mechanical self-test fixtures from spec v4 against the real emitter.

    With --full-fixtures (used in CI), F2/F4 run full C1..C7; locally without
    --full-fixtures, F2/F4 omit C3 (which has an unrelated 50ms wall-clock
    python plugin budget test that flakes under heavy shared-host CPU load) and
    C4 (covered by the CI suite) while still running C1, C2, C5, C6, C7.

    Progress is checkpointed per baseline check and fixture case; an interrupted
    run stays explicitly INCOMPLETE in the checkpoint and can never report
    fixture PASS.
    """
    spec = load_spec()
    checkpoint_path = checkpoint_path or checkpoint_sibling(logs)
    comment_subset = CHECK_ORDER if full_checks else ("C1", "C2", "C5", "C6", "C7")
    c5_runtime_subset = CHECK_ORDER if full_checks else ("C1", "C2", "C5", "C6", "C7")

    fixtures = [
        (
            "build_breaking",
            {
                "id": "F1_build_breaking",
                "backend": "llvm",
                "file": "lean/LeanNative/Backend/LLVM.lean",
                "search": "emitLine s!\"  {res} = sub{fl} {tyStr} {lVal}, {rVal}\"; return res",
                "replace": "emitLine (__B0_FIXTURE_BUILD_BREAK__); return res",
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
                "search": "emitLine s!\"  {res} = sub{fl} {tyStr} {lVal}, {rVal}\"; return res",
                "replace": "emitLine s!\"  {res} = sub{fl} {tyStr} {lVal}, {rVal}\"; return res -- B0 comment-only fixture",
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

    checkpoint = Checkpoint(checkpoint_path, {
        "schema": CHECKPOINT_SCHEMA,
        "kind": "fixtures",
        "full_checks": full_checks,
    })
    checkpoint.declare(
        "baseline:C1", "baseline:C2",
        *(f"fixture:{name}" for name, _, _, _ in fixtures),
    )

    fixture_logs = logs / "fixtures"
    if fixture_logs.exists():
        shutil.rmtree(fixture_logs)
    fixture_logs.mkdir(parents=True, exist_ok=True)

    parent = Path(tempfile.mkdtemp(prefix="emitter-mutant-fixtures-", dir=str(ROOT.parent)))
    results: dict[str, dict] = {}
    baseline_ok = False
    completed = False
    try:
        work = make_worktree(parent, "work")
        env = prepare_env(work, parent / "turbo-cache")

        base_checks, base_hashes, base_rebuild = run_pinned_checks(
            work, env, spec, fixture_logs / "baseline", check_subset=("C1", "C2"),
            on_check=lambda name, check: checkpoint.record(f"baseline:{name}", check),
        )
        snapshot = parent / "seed_lake_build"
        snapshot_lake_build(work, snapshot)
        baseline_ok = (
            base_checks["C1"]["exit"] == 0
            and base_checks["C2"]["exit"] == 0
            and base_rebuild["all_default_targets_built"]
        )
        checkpoint.record("baseline:outcome", {"baseline_compile_ok": baseline_ok})

        for name, mutation, subset, expected in fixtures:
            step = f"fixture:{name}"
            checkpoint.start(step)
            checkpoint.note(step, {"id": mutation["id"]})
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
                        work, env, spec, fixture_logs / name, check_subset=subset, lake_snapshot=snapshot,
                        on_check=lambda cname, check, step=step: checkpoint.note(step, {"checks": {cname: check}}),
                    )
                finally:
                    revert_worktree(work)
                outcome, killed_by, _ = classify(checks, order=subset)

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
            checkpoint.record(step, results[name])
        completed = True
        remove_worktree(work)
    finally:
        fixtures_report = {
            "schema": "emitter-mutants-fixtures-v1",
            "baseline_compile_ok": baseline_ok,
            "passed": completed and bool(results) and all(item["passed"] for item in results.values()),
            "fixtures": results,
        }
        if completed:
            checkpoint.finish("COMPLETED", {"passed": fixtures_report["passed"]})
        else:
            fixtures_report["run_outcome"] = "INCOMPLETE"
            fixtures_report["pending"] = list(checkpoint.payload["pending"])
            checkpoint.finish("INCOMPLETE", {"passed": False, "pending": list(checkpoint.payload["pending"])})
        git(["worktree", "prune"], ROOT, check=False)
        rmtree_writable(parent)
    return fixtures_report


def run_unit_tests() -> bool:
    """Exercise runner acceptance and provenance without requiring build tools."""
    import signal
    import sys
    import unittest
    from unittest.mock import Mock, patch

    class RunnerTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory()
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)
            self.spec = load_spec()

        def command(self, output: str, exit_code: int = 1) -> dict:
            return run_command(
                [sys.executable, "-c", f"print({output!r}); raise SystemExit({exit_code})"],
                self.root, os.environ.copy(), self.root / "command.log", self.spec["infra_signatures"],
            )

        def test_active_mutants_apply_to_current_sources(self):
            active = self.spec["mutations"]
            self.assertEqual({m["id"] for m in active}, {f"M{i}" for i in range(1, 11)})
            for mutation in active:
                with self.subTest(mutant=mutation["id"]):
                    self.assertEqual(mutation["expected_match_count"], 1)
                    source = ROOT / mutation["file"]
                    target = self.root / mutation["file"]
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(source, target)
                    before = target.read_text(encoding="utf-8")
                    self.assertEqual(before.count(mutation["search"]), 1)
                    # Isolate application from the checkout and only mock the
                    # reporting diff; exercise the runner's real patch function.
                    with patch(__name__ + ".git", return_value=subprocess.CompletedProcess([], 0, "fixture diff", "")):
                        count, diff = apply_patch(self.root, mutation)
                    self.assertEqual(count, 1)
                    self.assertTrue(diff)
                    self.assertEqual(target.read_text(encoding="utf-8"),
                        before.replace(mutation["search"], mutation["replace"], 1))
                    self.assertNotEqual(target.read_text(encoding="utf-8"), before)

        def test_stage_b_universe_is_live_applicable_mutants(self):
            # G5 Stage B (roadmap/GOALS.md): comparison_universe is exactly the
            # live mutants M1..M10 -- the retired not_applicable M11
            # (CAbiEmit.lean, removed in bf8ae24) must not linger in it.
            universe = list(self.spec["comparison_universe"])
            by_id = {m["id"]: m for m in self.spec["mutations"]}
            self.assertNotIn("M11", universe)
            self.assertEqual(tuple(universe), COMPARISON_UNIVERSE)
            self.assertEqual(set(by_id), set(universe))
            for mid in universe:
                with self.subTest(mutant=mid):
                    mutation = by_id[mid]
                    self.assertNotIn("not_applicable", mutation)
                    self.assertTrue((ROOT / mutation["file"]).is_file(), mutation["file"])

        def rows(self) -> list[dict]:
            return [{"id": mid, "backend": "llvm", "outcome": "SURVIVED"} for mid in COMPARISON_UNIVERSE]

        def summary(self, rows: list[dict], selected: list[str] | None = None, **kwargs) -> dict:
            return summarize(rows, self.spec, list(COMPARISON_UNIVERSE) if selected is None else selected, **kwargs)

        def signaled_command(self, sig=signal.SIGKILL) -> dict:
            return run_command(
                [sys.executable, "-c", f"import os; os.kill(os.getpid(), {int(sig)})"],
                self.root, os.environ.copy(), self.root / "signal.log", self.spec["infra_signatures"],
            )

        def test_signal_without_output_is_infra_failed_never_killed(self):
            for sig in (signal.SIGKILL, signal.SIGTERM):
                with self.subTest(signal=sig):
                    check = self.signaled_command(sig)
                    self.assertEqual(check["exit"], -sig)
                    self.assertEqual(check["log_tail"], "")
                    self.assertEqual(Path(check["log"]).read_text(), "")
                    self.assertEqual(check["infra_signature"], f"signal:{int(sig)}")
                    for name in ("C1", "C2", "C5"):
                        outcome, killed, infra = classify({"C3": self.command("assertion failed"), name: check})
                        self.assertEqual((outcome, killed, infra), ("INFRA_FAILED", [], [name]))
                        rows = self.rows()
                        self.assertTrue(self.summary(rows)["conclusive"])
                        rows[0].update(outcome=outcome, infra_failed_checks=infra)
                        summary = self.summary(rows)
                        self.assertEqual(summary["run_outcome"], "INCONCLUSIVE")
                        self.assertFalse(summary["conclusive"])
                        self.assertEqual(summary["kill_rate_per_backend"]["llvm"]["killed"], 0)

        def test_baseline_signal_marks_whole_run_infra_failed(self):
            check = self.signaled_command()
            for name in ("C1", "C5"):
                with self.subTest(check=name), patch.multiple(
                    __name__,
                    make_worktree=Mock(return_value=self.root),
                    remove_worktree=Mock(),
                    git=Mock(return_value=subprocess.CompletedProcess([], 0, "test-sha\n", "")),
                    toolchain=Mock(return_value={}),
                    c5_flag_check=Mock(return_value={}),
                    run_pinned_checks=Mock(return_value=({name: check}, {}, {"all_default_targets_built": True})),
                    evaluate_mutation=Mock(side_effect=AssertionError("mutations must not run after baseline failure")),
                ):
                    output = self.root / "report.json"
                    report = run_suite(output, self.root / "logs")
                    self.assertEqual(json.loads(output.read_text()), report)
                    self.assertEqual(report["baseline"]["outcome"], "INFRA_FAILED")
                    self.assertEqual(report["baseline"]["failed_checks"], [name])
                    self.assertEqual(report["run_outcome"], "INFRA_FAILED")
                    self.assertFalse(report["summary"]["conclusive"])
                    self.assertEqual(report["kill_rate_per_backend"], {})
                    self.assertEqual(report["mutations"], [])

        # Durable atomic report checkpoints (suite/fixtures, per check/case).

        def synthetic_spec(self) -> dict:
            return dict(self.spec, checks={
                name: {"argv": [sys.executable, "-c", "pass"], "depends_on": []}
                for name in CHECK_ORDER
            })

        def primed_hash_builds(self) -> Mock:
            state = {"primed": False}

            def fake(root):
                if not state["primed"]:
                    state["primed"] = True
                    return {path: None for path in ALL_HASH_PATHS}
                return {path: "primed-sha" for path in ALL_HASH_PATHS}

            return Mock(side_effect=fake)

        def suite_mocks(self, spec: dict, **overrides):
            mocks = {
                "load_spec": Mock(return_value=spec),
                "make_worktree": Mock(return_value=self.root),
                "remove_worktree": Mock(),
                "git": Mock(return_value=subprocess.CompletedProcess([], 0, "test-sha\n", "")),
                "toolchain": Mock(return_value={}),
                "c5_flag_check": Mock(return_value={}),
                "snapshot_lake_build": Mock(),
                "hash_builds": self.primed_hash_builds(),
            }
            mocks.update(overrides)
            return patch.multiple(__name__, **mocks)

        def killed_record(self, mutation: dict) -> dict:
            return {"id": mutation["id"], "backend": mutation["backend"], "outcome": "KILLED", "killed_by": ["C3"], "checks": {}}

        def clean_check(self) -> dict:
            return {"exit": 0, "infra_signature": None}

        def fixtures_mocks(self, spec: dict, responses: list) -> object:
            calls = {"n": 0}

            def runner(root, env, spec, log_dir, check_subset=CHECK_ORDER, lake_snapshot=None, on_check=None):
                response = responses[calls["n"]]
                calls["n"] += 1
                if isinstance(response, BaseException):
                    raise response
                if on_check is not None:
                    for name, check in response[0].items():
                        on_check(name, dict(check))
                return response

            return patch.multiple(
                __name__,
                load_spec=Mock(return_value=spec),
                make_worktree=Mock(return_value=self.root),
                remove_worktree=Mock(),
                git=Mock(return_value=subprocess.CompletedProcess([], 0, "test-sha\n", "")),
                snapshot_lake_build=Mock(),
                revert_worktree=Mock(),
                apply_patch=Mock(side_effect=lambda work, mutation: (0, "") if mutation["id"] == "F3_non_matching" else (1, "diff")),
                run_pinned_checks=Mock(side_effect=runner),
            )

        def test_checkpoint_sibling_lives_beside_its_report(self):
            self.assertEqual(checkpoint_sibling(Path("/x/report.json")), Path("/x/report.json.checkpoint.json"))
            self.assertEqual(checkpoint_sibling(Path("/x/logs")), Path("/x/logs.checkpoint.json"))

        def test_atomic_checkpoint_write_never_tears_or_erases_evidence(self):
            path = self.root / "cp.json"
            atomic_write_json(path, {"v": 1})
            self.assertEqual(json.loads(path.read_text()), {"v": 1})
            with patch(__name__ + ".json.dump", Mock(side_effect=TypeError("no serialization"))):
                with self.assertRaises(TypeError):
                    atomic_write_json(path, {"v": 2})
            self.assertEqual(json.loads(path.read_text()), {"v": 1})
            self.assertEqual(list(self.root.iterdir()), [path])

        def test_suite_checkpoints_before_work_after_each_check_and_on_completion(self):
            spec = self.synthetic_spec()
            output = self.root / "report.json"
            checkpoint_path = checkpoint_sibling(output)
            before_work = {}

            def spy_worktree(parent, name):
                before_work["checkpoint"] = json.loads(checkpoint_path.read_text())
                return self.root

            with self.suite_mocks(
                spec,
                make_worktree=Mock(side_effect=spy_worktree),
                run_command=Mock(return_value={"exit": 0, "wall_s": 0.25, "log_tail": "ok", "log": "x", "infra_signature": None}),
                evaluate_mutation=Mock(side_effect=lambda root, mutation, *args, **kwargs: self.killed_record(mutation)),
            ):
                report = run_suite(output, self.root / "logs")
            self.assertEqual(
                before_work["checkpoint"]["pending"],
                sorted(["provenance", *(f"baseline:{name}" for name in CHECK_ORDER), *(f"mutant:M{i}" for i in range(1, 11))]),
            )
            self.assertEqual(before_work["checkpoint"]["steps"], {})
            self.assertFalse(before_work["checkpoint"]["complete"])
            self.assertEqual(before_work["checkpoint"]["run_outcome"], "INCOMPLETE")
            checkpoint = json.loads(checkpoint_path.read_text())
            self.assertTrue(checkpoint["complete"])
            self.assertEqual(checkpoint["run_outcome"], report["run_outcome"])
            self.assertEqual(checkpoint["pending"], [])
            self.assertEqual(checkpoint["steps"]["provenance"]["commit"], "test-sha")
            for name in CHECK_ORDER:
                step = checkpoint["steps"][f"baseline:{name}"]
                self.assertEqual((step["exit"], step["wall_s"]), (0, 0.25))
            self.assertEqual(checkpoint["steps"]["baseline:outcome"]["outcome"], "PASSED")
            for mid in COMPARISON_UNIVERSE:
                self.assertEqual(checkpoint["steps"][f"mutant:{mid}"]["outcome"], "KILLED")
            self.assertEqual(json.loads(output.read_text()), report)

        def test_suite_interruption_keeps_completed_evidence_and_explicit_pending(self):
            spec = self.synthetic_spec()
            output = self.root / "report.json"
            checkpoint_path = checkpoint_sibling(output)
            with self.suite_mocks(
                spec,
                run_command=Mock(return_value={"exit": 0, "wall_s": 0.25, "log_tail": "ok", "log": "x", "infra_signature": None}),
                evaluate_mutation=Mock(side_effect=KeyboardInterrupt),
            ):
                with self.assertRaises(KeyboardInterrupt):
                    run_suite(output, self.root / "logs", only_ids=["M1"], check_subset=CHECK_ORDER)
            checkpoint = json.loads(checkpoint_path.read_text())
            self.assertFalse(checkpoint["complete"])
            self.assertEqual(checkpoint["run_outcome"], "INCOMPLETE")
            for name in CHECK_ORDER:
                step = checkpoint["steps"][f"baseline:{name}"]
                self.assertEqual((step["exit"], step["wall_s"]), (0, 0.25))
            self.assertEqual(checkpoint["steps"]["baseline:outcome"]["outcome"], "PASSED")
            active = checkpoint["steps"]["mutant:M1"]
            self.assertEqual((active["status"], active["complete"], active["id"]), ("INCOMPLETE", False, "M1"))
            self.assertIn("mutant:M1", checkpoint["pending"])
            report = json.loads(output.read_text())
            self.assertEqual(report["run_outcome"], "INCOMPLETE")
            self.assertNotIn(report["run_outcome"], ("CONCLUSIVE", "TARGETED", "INFRA_FAILED"))
            self.assertFalse(report["summary"]["conclusive"])
            self.assertEqual(report["summary"]["run_outcome"], "INCOMPLETE")
            self.assertEqual(report["summary"]["pending"], checkpoint["pending"])
            self.assertEqual(report["kill_rate_per_backend"], {})

        def test_fixture_checkpoints_complete_with_pass_summary(self):
            spec = self.synthetic_spec()
            checkpoint_path = self.root / "fixtures.checkpoint.json"
            hashes = {"lean/.lake/build/bin/lean-native-core": "primed"}
            baseline = ({"C1": self.clean_check(), "C2": self.clean_check()}, dict(hashes), {"all_default_targets_built": True})
            responses = [
                baseline,
                ({"C1": {"exit": 1, "infra_signature": None}}, dict(hashes), {"all_default_targets_built": True}),
                ({name: self.clean_check() for name in ("C1", "C2", "C5", "C6", "C7")}, dict(hashes), {"all_default_targets_built": True}),
                (
                    {**{name: self.clean_check() for name in ("C1", "C2", "C6", "C7")}, "C5": {"exit": 1, "infra_signature": None}},
                    {**hashes, "lean/.lake/build/bin/lean-native-core": "mutant"},
                    {"all_default_targets_built": True},
                ),
            ]
            with self.fixtures_mocks(spec, responses):
                report = run_fixtures(self.root / "flogs", checkpoint_path=checkpoint_path)
            self.assertTrue(report["passed"])
            self.assertNotIn("run_outcome", report)
            checkpoint = json.loads(checkpoint_path.read_text())
            self.assertTrue(checkpoint["complete"])
            self.assertEqual(checkpoint["run_outcome"], "COMPLETED")
            self.assertEqual(checkpoint["pending"], [])
            self.assertTrue(checkpoint["summary"]["passed"])
            self.assertEqual(checkpoint["steps"]["fixture:build_breaking"]["outcome"], "KILLED")
            self.assertEqual(checkpoint["steps"]["fixture:runtime_only_c5"]["killed_by"], ["C5"])
            self.assertEqual(checkpoint["steps"]["fixture:non_matching"]["outcome"], "APPLY_FAILED")

        def test_fixture_interruption_marks_cases_incomplete_and_never_passes(self):
            spec = self.synthetic_spec()
            checkpoint_path = self.root / "fixtures.checkpoint.json"
            baseline = ({"C1": self.clean_check(), "C2": self.clean_check()}, {}, {"all_default_targets_built": True})
            with self.fixtures_mocks(spec, [baseline, KeyboardInterrupt()]):
                with self.assertRaises(KeyboardInterrupt):
                    run_fixtures(self.root / "flogs", checkpoint_path=checkpoint_path)
            checkpoint = json.loads(checkpoint_path.read_text())
            self.assertFalse(checkpoint["complete"])
            self.assertEqual(checkpoint["run_outcome"], "INCOMPLETE")
            self.assertTrue(checkpoint["steps"]["baseline:outcome"]["baseline_compile_ok"])
            active = checkpoint["steps"]["fixture:build_breaking"]
            self.assertEqual((active["status"], active["complete"]), ("INCOMPLETE", False))
            self.assertIn("fixture:build_breaking", checkpoint["pending"])
            for name in ("comment_only", "non_matching", "runtime_only_c5"):
                self.assertIn(f"fixture:{name}", checkpoint["pending"])
                self.assertNotIn(f"fixture:{name}", checkpoint["steps"])
            self.assertIs(checkpoint["summary"]["passed"], False)

        def test_c1_oom_and_c5_missing_engines_is_infra_failed(self):
            checks = {
                "C1": self.command("out of memory"),
                "C2": self.command("built", 0),
                "C5": self.command("Required conformance engines unavailable"),
            }
            outcome, killed, infra = classify(checks)
            self.assertEqual((outcome, killed, infra), ("INFRA_FAILED", [], ["C1"]))
            rows = self.rows()
            rows[0].update(outcome=outcome, infra_failed_checks=infra)
            self.assertFalse(self.summary(rows)["conclusive"])
            # Reject older mixed-outcome reports too, even if their outcome says KILLED.
            rows[0]["outcome"] = "KILLED"
            self.assertFalse(self.summary(rows)["conclusive"])

        def test_failed_build_skips_subsequent_checks(self):
            for failed in ("C1", "C2"):
                with self.subTest(failed=failed):
                    spec = dict(self.spec, checks={
                        name: {"argv": [sys.executable, "-c", (
                            "print('out of memory'); raise SystemExit(1)" if name == failed else
                            "print('Required conformance engines unavailable'); raise SystemExit(1)" if name == "C5" else
                            "pass"
                        )], "depends_on": []}
                        for name in CHECK_ORDER
                    })
                    checks, _, _ = run_pinned_checks(self.root, os.environ.copy(), spec, self.root / failed)
                    for name in CHECK_ORDER[CHECK_ORDER.index(failed) + 1:]:
                        self.assertEqual(checks[name]["status"], "SKIPPED_PREREQ")
                        self.assertIsNone(checks[name]["exit"])
                        self.assertFalse((self.root / failed / f"{name}.log").exists())
                    self.assertEqual(classify(checks), ("INFRA_FAILED", [], [failed]))

        def test_oom_before_more_than_4000_diagnostic_chars(self):
            check = self.command("out of memory\n" + "diagnostic\n" * 500)
            self.assertEqual(len(check["log_tail"]), LOG_TAIL)
            self.assertNotIn("out of memory", check["log_tail"])
            self.assertIn("out of memory", Path(check["log"]).read_text())
            self.assertEqual(classify({"C1": check}), ("INFRA_FAILED", [], ["C1"]))

        def test_infra_overrides_kill_in_either_order(self):
            for first, second in (("out of memory", "assertion failed"), ("assertion failed", "out of memory")):
                with self.subTest(first=first):
                    outcome, killed, infra = classify({"C3": self.command(first), "C5": self.command(second)})
                    self.assertEqual(outcome, "INFRA_FAILED")
                    self.assertEqual(killed, [])
                    self.assertEqual(len(infra), 1)
            self.assertEqual(classify({"C5": self.command("out of memory", 0)})[0], "INFRA_FAILED")

        def test_non_infra_build_failure_is_killed_only_by_prerequisite(self):
            self.assertEqual(classify({
                "C1": self.command("unknown identifier"),
                "C5": self.command("Required conformance engines unavailable"),
            }), ("KILLED", ["C1"], []))

        def test_only_m1_is_targeted_never_conclusive(self):
            summary = self.summary(self.rows()[:1], ["M1"])
            self.assertFalse(summary["conclusive"])
            self.assertEqual(summary["run_outcome"], "TARGETED")
            self.assertEqual(summary["missing_universe_ids"], list(COMPARISON_UNIVERSE[1:]))
            summary = self.summary(self.rows(), targeted=True)
            self.assertFalse(summary["conclusive"])
            self.assertEqual(summary["run_outcome"], "TARGETED")

        def test_fixed_universe_acceptance(self):
            rows = self.rows()
            rows[1]["outcome"] = "KILLED"
            self.assertTrue(self.summary(rows)["conclusive"])
            for invalid in (rows[:-1], rows + [rows[0]], rows + [dict(rows[0], id="M11")]):
                self.assertFalse(self.summary(invalid)["conclusive"])

        def test_emitter_module_hashes_record_changes(self):
            self.assertEqual(set(self.spec["hash_paths"]), set(ALL_HASH_PATHS))
            for relative in EMITTER_MODULES:
                self.assertIn(relative, self.spec["checks"]["C1"]["depends_on"])
                path = self.root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"baseline")
                before = hash_builds(self.root)
                path.write_bytes(b"mutant")
                self.assertNotEqual(before[relative], hash_builds(self.root)[relative])

        def test_c5_flag_check_verifies_tier_support_and_unknown_tier_rejection(self):
            flag_res = c5_flag_check(ROOT, os.environ.copy())
            self.assertTrue(flag_res["tier_flag_supported"], flag_res)
            self.assertTrue(flag_res["unknown_tier_rejected"], flag_res)
            self.assertFalse(flag_res["used_by_C5"])

        def test_verify_kills_uses_full_check_order(self):
            import io
            from contextlib import redirect_stdout
            captured = {}

            def fake_run_suite(out_path, logs_path, only_ids=None, check_subset=CHECK_ORDER):
                captured["check_subset"] = tuple(check_subset)
                active_expected = len(self.spec["mutations"])
                return {
                    "run_outcome": "CONCLUSIVE",
                    "summary": {"counts": {"KILLED": active_expected, "SURVIVED": 0}},
                }

            buf = io.StringIO()
            with patch(__name__ + ".run_unit_tests", return_value=True), patch(
                __name__ + ".run_suite", side_effect=fake_run_suite
            ), patch.object(sys, "argv", ["emitter_mutants.py", "--verify-kills"]), redirect_stdout(buf):
                rc = main()
            self.assertEqual(rc, 0)
            self.assertEqual(captured["check_subset"], CHECK_ORDER)
            self.assertEqual(json.loads(buf.getvalue())["check_subset"], list(CHECK_ORDER))

    return unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RunnerTests)).wasSuccessful()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--unit-tests", action="store_true", help="run runner regression tests without build tools")
    parser.add_argument("--verify-kills", action="store_true", help="run unit tests and full B-3 mutation suite requiring 100% active mutant kills")
    parser.add_argument("--fixtures", action="store_true", help="run the 4 required self-test fixtures")
    parser.add_argument("--full-fixtures", action="store_true", help="include C3/C4 in F2/F4 fixtures (for CI)")
    parser.add_argument("--fixtures-output", type=Path, help="optional path to write fixture JSON report")
    parser.add_argument("--only", help="comma-separated subset of mutation IDs for targeted testing")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--logs", type=Path, default=None)
    args = parser.parse_args()

    if args.unit_tests:
        return 0 if run_unit_tests() else 1

    if args.fixtures:
        fix_tmp = tempfile.TemporaryDirectory(prefix="emitter-fixtures-logs-") if args.logs is None else None
        try:
            logs_path = args.logs or Path(fix_tmp.name)
            anchor = args.fixtures_output or args.logs or (ROOT / "emitter-mutation-fixtures.json")
            report = run_fixtures(logs_path, full_checks=args.full_fixtures, checkpoint_path=checkpoint_sibling(anchor))
            text = json.dumps(report, indent=2, sort_keys=True) + "\n"
            if args.fixtures_output:
                args.fixtures_output.parent.mkdir(parents=True, exist_ok=True)
                args.fixtures_output.write_text(text, encoding="utf-8")
            print(text, end="")
            return 0 if report["passed"] else 1
        finally:
            if fix_tmp is not None:
                fix_tmp.cleanup()

    only_ids = [item.strip() for item in args.only.split(",") if item.strip()] if args.only else None
    if args.verify_kills:
        if not run_unit_tests():
            return 1
        active_expected = len(load_spec()["mutations"])
        verify_subset = CHECK_ORDER
        tmp_ctx = tempfile.TemporaryDirectory(prefix="emitter-verify-kills-") if (args.output is None and args.logs is None) else None
        try:
            base_dir = Path(tmp_ctx.name) if tmp_ctx is not None else ROOT
            out_path = args.output or (base_dir / "emitter-mutation-report.json")
            logs_path = args.logs or (base_dir / "emitter-mutation-logs")
            report = run_suite(out_path, logs_path, only_ids=only_ids, check_subset=verify_subset)
            counts = report.get("summary", {}).get("counts", {})
            all_killed = (
                report["run_outcome"] == "CONCLUSIVE"
                and counts.get("SURVIVED", 0) == 0
                and counts.get("KILLED", 0) == active_expected
            )
            print(
                json.dumps(
                    {
                        "all_active_killed": all_killed,
                        "check_subset": list(verify_subset),
                        "expected_active_kills": active_expected,
                        "run_outcome": report["run_outcome"],
                        "summary": report.get("summary", {}),
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0 if all_killed else 1
        finally:
            if tmp_ctx is not None:
                rmtree_writable(Path(tmp_ctx.name))
                tmp_ctx.cleanup()

    out_path = args.output or (ROOT / "emitter-mutation-report.json")
    logs_path = args.logs or (ROOT / "emitter-mutation-logs")
    report = run_suite(out_path, logs_path, only_ids=only_ids)
    print(
        json.dumps(
            {
                "output": str(out_path),
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
