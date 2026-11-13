#!/usr/bin/env python3
"""Measure CLI wallclock (including startup), proof edits, and eight-agent checks.

Cold means an empty per-case turbo store, not a cold OS page cache or Lake build.
Source edits are restored in finally blocks. Failures and unmet latency goals are
reported, never dropped from the artifact. Linux PSS is sampled across the CLI
process trees and persistent zygote workers, counting each PID once.
"""

import argparse
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import tempfile
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PHASES = (
    "hygiene_ms", "import_refresh_ms", "identity_ms", "cache_ms",
    "elab_ms", "kernel_ms",
)


def check(binary, project, file, cache, timeout, decl=None, workload=None):
    command = [str(binary), "check", str(file), "--json", "--project-dir",
               str(project), "--cache-dir", str(cache), "--timeout", str(timeout)]
    if decl:
        command += ["--decl", decl]
    start = time.perf_counter()
    env = os.environ.copy()
    if workload:
        env["TURBO_WALLCLOCK_WORKLOAD"] = workload
        env["TURBO_LEAN_FORK_EVIDENCE"] = str(cache / "fork-evidence.log")
    try:
        proc = subprocess.run(command, capture_output=True, text=True,
                              timeout=timeout + 30, check=False, env=env)
        external = (time.perf_counter() - start) * 1000
        if proc.returncode:
            return {"ok": False, "external_wall_ms": external,
                    "error": proc.stderr.strip(), "returncode": proc.returncode}
        result = json.loads(proc.stdout)
        assert result["wall_ms"] >= result["elapsed_ms"]
        assert all(result["phases"][key] >= 0 for key in PHASES)
        return {"ok": True, "external_wall_ms": external, **result}
    except (subprocess.TimeoutExpired, ValueError, KeyError, AssertionError) as err:
        return {"ok": False, "external_wall_ms": (time.perf_counter() - start) * 1000,
                "error": str(err)}


def proof_edit(source, decl):
    """Insert a real no-op tactic inside an existing proof, not a trailing comment."""
    name = re.escape(decl.rsplit(".", 1)[-1]) if decl else r"[^\s:(]+"
    match = re.search(r"\b(?:theorem|lemma)\s+" + name
                      + r"(?=\s|\()[\s\S]*?:=\s*by\b", source)
    if not match:
        raise ValueError("no tactic proof found for reversible body edit")
    pos = match.end()
    return source[:pos] + " skip;" + source[pos:]


def latency_case(args, project, relative, decl, cache):
    file = project / relative
    row = {"project": str(project), "file": relative, "decl": decl}
    if not file.is_file():
        return {**row, "error": "missing prewarmed input"}
    source = file.read_bytes()
    for mode in ("cold", "warm_cache"):
        row[mode] = check(args.binary, project, file, cache, args.timeout, decl)
    try:
        file.write_text(proof_edit(source.decode(), decl))
        row["warm_edit"] = check(args.binary, project, file, cache, args.timeout, decl)
    except ValueError as err:
        row["warm_edit"] = {"ok": False, "error": str(err)}
    finally:
        file.write_bytes(source)
    row["warm_cache_under_100_ms"] = (
        row["warm_cache"]["ok"] and row["warm_cache"]["wall_ms"] < 100)
    row["warm_edit_under_500_ms"] = (
        row["warm_edit"]["ok"] and row["warm_edit"]["wall_ms"] < 500)
    return row


def sample_pss(stop, peak, workload):
    # Inherited by children and persistent daemons, unlike ancestry after reparenting.
    marker = f"TURBO_WALLCLOCK_WORKLOAD={workload}".encode()
    while not stop.wait(0.025):
        total = 0
        for proc in Path("/proc").iterdir():
            if not proc.name.isdigit():
                continue
            try:
                if marker not in (proc / "environ").read_bytes().split(b"\0"):
                    continue
                for line in (proc / "smaps_rollup").read_text().splitlines():
                    if line.startswith("Pss:"):
                        total += int(line.split()[1])
            except (OSError, ProcessLookupError):
                continue
        peak[0] = max(peak[0], total / 1024)


def concurrency(args, cache):
    # Unique theorem bodies force work beyond attested receipt cache hits while
    # sharing an identical imported environment/prefix in the persistent pool.
    with tempfile.TemporaryDirectory(prefix="wallclock-agents-") as tmp:
        imported_module = args.agent_import
        project = Path(tmp)
        # Daemon identity includes the executable path. Give this workload its
        # own daemon so inherited PSS markers and fork evidence cannot point at
        # an unrelated daemon started by an earlier benchmark.
        binary = project / "turbo-lean"
        shutil.copy2(args.binary, binary)
        (project / "lean-toolchain").write_bytes(
            (args.batteries_dir / "lean-toolchain").read_bytes())
        (project / "lakefile.toml").write_text(
            'name = "wallclock_agents"\n[[require]]\nname = "batteries"\n'
            'git = "https://github.com/leanprover-community/batteries.git"\n'
            '[[lean_lib]]\nname = "Agent"\n')
        revision = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=args.batteries_dir, text=True).strip()
        packages = project / ".lake/packages"
        packages.mkdir(parents=True)
        (packages / "batteries").symlink_to(args.batteries_dir, target_is_directory=True)
        (project / "lake-manifest.json").write_text(json.dumps({
            "version": "1.2.0", "packagesDir": ".lake/packages",
            "name": "wallclock_agents", "lakeDir": ".lake",
            "packages": [{"type": "git", "name": "batteries",
                          "url": "https://github.com/leanprover-community/batteries.git",
                          "rev": revision, "inputRev": revision, "subDir": None,
                          "manifestFile": "lake-manifest.json",
                          "configFile": "lakefile.toml", "inherited": False}]}))
        directory = project
        files = []
        for i in range(8):
            file = directory / f"Agent{i}.lean"
            file.write_text(f"import {imported_module}\n"
                            f"theorem agent_work : {i} = {i} := by rfl\n")
            files.append(file)
        # Materialize the exact shared import closure before launching clients.
        # Lake publication during the measured window would benchmark a build
        # race rather than eight checks against one stable environment.
        prepared = subprocess.run(
            ["lake", "build", f"+{imported_module}"], cwd=project,
            capture_output=True, text=True, timeout=args.timeout + 30, check=False)
        if prepared.returncode:
            raise RuntimeError("concurrency import preparation failed: " + prepared.stderr)
        workload = uuid.uuid4().hex
        warmup = check(binary, project, files[0], cache, args.timeout,
                       "agent_work", workload)
        evidence = cache / "fork-evidence.log"
        # Warmup is not evidence that any of the eight measured checks forked.
        if evidence.is_file():
            evidence.write_text("")
        for i, file in enumerate(files):
            file.write_text(f"import {imported_module}\n"
                            f"theorem agent_work : {i + 100} = {i + 100} := by rfl\n")
        stop = threading.Event()
        peak = [0.0]
        sampler = threading.Thread(target=sample_pss, args=(stop, peak, workload))
        sampler.start()
        try:
            with ThreadPoolExecutor(max_workers=8) as executor:
                results = list(executor.map(
                    lambda file: check(binary, project, file, cache,
                                        args.timeout, "agent_work", workload), files))
        finally:
            stop.set()
            sampler.join()
        fork_requests = evidence.read_text().splitlines() if evidence.is_file() else []
    walls = sorted(result["external_wall_ms"] for result in results)
    return {"work_units": len(results),
             "imported_module": imported_module,
            "error_count": sum(not result["ok"] for result in results),
            "total_pss_mb": round(peak[0], 2),
            "wall_p50_ms": statistics.median(walls),
            "wall_p95_ms": walls[math.ceil(0.95 * len(walls)) - 1],
             "pss_scope": "peak summed Linux PSS of uniquely marked workload processes",
             "cow_fork_verified": bool(fork_requests),
             "successful_fork_requests": fork_requests,
            "warmup": warmup, "results": results}


def markdown(report):
    print("| Input | Mode | wall_ms | elapsed_ms | external ms | Result |")
    print("|---|---|---:|---:|---:|---|")
    for row in report["latency"]:
        label = row["file"] + (" --decl " + row["decl"] if row["decl"] else "")
        for mode in ("cold", "warm_cache", "warm_edit"):
            value = row.get(mode, {})
            external = value.get("external_wall_ms", 0)
            print(f"| {label} | {mode} | {value.get('wall_ms', '—')} | "
                  f"{value.get('elapsed_ms', '—')} | {external:.1f} | "
                  f"{'OK' if value.get('ok') else 'ERROR'} |")
            if value.get("ok"):
                print("<!-- phases " + json.dumps(value["phases"], sort_keys=True) + " -->")
    keys = ("work_units", "error_count", "total_pss_mb", "wall_p50_ms", "wall_p95_ms")
    print("\n| " + " | ".join(keys) + " |")
    print("|" + "---|" * len(keys))
    print("| " + " | ".join(str(report["concurrency"][key]) for key in keys) + " |")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/turbo-lean")
    parser.add_argument("--batteries-dir", type=Path,
                        default=Path("/var/lib/orb-node/work/bench/batteries"))
    parser.add_argument("--pfr-dir", type=Path,
                        default=Path("/var/lib/orb-node/work/bench/pfr"))
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--agent-import", default="Batteries.Data.List.Lemmas",
                        choices=["Batteries.Data.List.Basic", "Batteries.Data.List.Lemmas"],
                        help="Explicit workload scope; Basic results do not satisfy Lemmas acceptance")
    args = parser.parse_args()
    if not args.binary.is_file():
        parser.error("build the release binary or pass --binary")
    if not args.batteries_dir.is_dir():
        parser.error("missing Batteries checkout; pass --batteries-dir")
    cases = [(args.batteries_dir, "Batteries/Data/List/Basic.lean", "List.headD_eq_head?"),
             (args.batteries_dir, "Batteries/Data/List/Basic.lean", None),
             (args.batteries_dir, "Batteries/Data/List/Lemmas.lean", None),
             (args.pfr_dir, "PFR/Mathlib/Probability/IdentDistrib.lean", None)]
    with tempfile.TemporaryDirectory(prefix="turbo-wallclock-") as tmp:
        report = {"schema_version": 1, "binary": str(args.binary),
                  "cpu_count": os.cpu_count(), "latency": [
                      latency_case(args, project, file, decl, Path(tmp) / str(i))
                      for i, (project, file, decl) in enumerate(cases)]}
        report["concurrency"] = concurrency(args, Path(tmp) / "agents")
    markdown(report)
    if args.json_out:
        args.json_out.write_text(json.dumps(report, indent=2) + "\n")
    return int(any(not row.get("warm_cache_under_100_ms", False)
                   or not row.get("warm_edit_under_500_ms", False)
                   for row in report["latency"])
               or report["concurrency"]["error_count"] != 0
               or not report["concurrency"]["cow_fork_verified"])


if __name__ == "__main__":
    raise SystemExit(main())
