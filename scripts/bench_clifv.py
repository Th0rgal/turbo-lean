#!/usr/bin/env python3
"""Linux paired clifv benchmark. No third-party runtime dependencies."""
import argparse
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import random
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import uuid

SCENARIOS = ("cold", "warm", "proof", "statement", "import")
EDIT_FILE = "FV/E2E/RegLevelCountIWitness.lean"
THEOREM = """theorem iterN_stepC_id : iterN (stepC (fun _ => True) (id : Unit → Unit)) 4 ((), 7) = ((), 11) := by
  rw [iterN_stepC, countIn_true]"""


def edited_source(source, scenario):
    if source.count(THEOREM) != 1:
        raise ValueError(f"{EDIT_FILE}: pinned edit anchor changed; review the fixture before benchmarking")
    if scenario == "proof":
        return source.replace(THEOREM, THEOREM.replace("rw [", "simpa only ["))
    if scenario == "statement":
        return source.replace(THEOREM, THEOREM.replace("4 ((), 7) = ((), 11)", "5 ((), 7) = ((), 12)"))
    if scenario == "import":
        return "import Init\n" + source
    return source


def capture(cmd, cwd=None, env=None):
    return subprocess.check_output(cmd, cwd=cwd, env=env, text=True).strip()


def stats(values):
    mean = statistics.mean(values)
    return {"mean": mean, "median": statistics.median(values),
            "cv": statistics.stdev(values) / mean if len(values) > 1 and mean > 0 else None}


def summarize(pairs):
    metrics = {arm: {metric: stats([p[arm][metric] for p in pairs])
                     for metric in ("wall_s", "cpu_s", "peak_rss_kib")} for arm in ("stock", "turbo")}
    reasons = []
    if any(p["parity"] == "INVALID" for p in pairs):
        reasons.append("INVALID pair")
    if any(p[a]["exit_code"] != 0 for p in pairs for a in ("stock", "turbo")):
        reasons.append("failed workload")
    # CV gates wall, CPU and RSS in BOTH arms, plus the paired wall ratios.
    ratios = [p["stock"]["wall_s"] / p["turbo"]["wall_s"] for p in pairs
              if p["turbo"]["wall_s"] > 0]
    ratio_stats = stats(ratios) if len(ratios) == len(pairs) else None
    cvs = [s["cv"] for arm in metrics.values() for s in arm.values()]
    cvs.append(ratio_stats["cv"] if ratio_stats else None)
    if any(c is None for c in cvs):
        reasons.append("insufficient or zero-valued measurements")
    elif any(c > 0.10 for c in cvs):
        reasons.append("CV > 10%")
    ratio = None
    if not reasons:
        rng = random.Random(0)
        boot = sorted(statistics.mean(rng.choices(ratios, k=len(ratios))) for _ in range(10000))
        ratio = {"mean": ratio_stats["mean"], "median": ratio_stats["median"],
                 "cv": ratio_stats["cv"], "bootstrap_95_ci": [boot[249], boot[9749]],
                 "bootstrap_samples": 10000, "seed": 0}
    return {"metrics": metrics, "paired_wall_ratio": ratio,
            "ratio_suppressed_reasons": reasons, "speedup_claim_allowed": not reasons}


def pair_record(index, stock, turbo):
    # A failed measurement is not a Lean verdict, even if both arms fail alike.
    valid = (stock["measurement_ok"] and turbo["measurement_ok"]
             and ((stock["exit_code"] == 0) == (turbo["exit_code"] == 0)))
    return {"index": index, "order": ["stock", "turbo"], "stock": stock, "turbo": turbo,
            "parity": ("PASS" if stock["exit_code"] == 0 else "FAIL") if valid else "INVALID"}


def write_report(report, output):
    invalid = any(p["parity"] == "INVALID" for s in report["scenarios"] for p in s["pairs"])
    for scenario in report["scenarios"]:
        scenario["summary"] = summarize(scenario["pairs"])
        reasons = scenario["summary"]["ratio_suppressed_reasons"]
        if invalid:
            reasons.append("INVALID pair in experiment")
        if report["status"] != "complete":
            reasons.append("incomplete experiment")
        if reasons:
            scenario["summary"].update(paired_wall_ratio=None, speedup_claim_allowed=False)
    output.mkdir(parents=True, exist_ok=True)
    path = output / "results.json"
    tmp = output / "results.json.tmp"
    tmp.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    tmp.replace(path)
    lines = ["# clifv paired benchmark", "", f"Status: {report['status']}. Telemetry: off.", "",
             "A = stock `lake build`; B = `turbo-lean " + report["turbo_command"] + "`. Order: ABAB….",
             "Ratio = arithmetic mean of paired stock/turbo wall times; values > 1 favor turbo.",
             "CPU and RSS cover the timed command and waited-for children; detached daemons may be excluded.",
             "", "## Provenance", "", "```json", json.dumps(report["machine"], indent=2), "```", ""]
    for scenario in report["scenarios"]:
        lines += [f"## {scenario['name']}", "", "| Arm | Metric | Mean | Median | CV |",
                  "|---|---|---:|---:|---:|"]
        summary = scenario["summary"]
        for arm, metrics in summary["metrics"].items():
            for metric, s in metrics.items():
                cv = "n/a" if s["cv"] is None else f"{100*s['cv']:.2f}%"
                lines.append(f"| {arm} | {metric} | {s['mean']:.6g} | {s['median']:.6g} | {cv} |")
        ratio = summary["paired_wall_ratio"]
        if ratio:
            lo, hi = ratio["bootstrap_95_ci"]
            lines += ["", f"Paired wall ratio: {ratio['mean']:.3f}× (bootstrap 95% CI {lo:.3f}–{hi:.3f})."]
        else:
            lines += ["", "Speedup/ratio withheld: " + "; ".join(summary["ratio_suppressed_reasons"]) + "."]
        lines += ["", "| Pair | Stock exit | Turbo exit | Verdict parity |",
                  "|---:|---:|---:|---|"]
        for p in scenario["pairs"]:
            lines.append(f"| {p['index']} | {p['stock']['exit_code']} | {p['turbo']['exit_code']} | {p['parity']} |")
        lines += [""]
    (output / "results.md").write_text("\n".join(lines) + "\n")


def machine_info():
    return {"hostname": os.uname().nodename, "platform": " ".join(os.uname()),
            "nproc": int(capture(["nproc"])), "mem_total_kib": int(re.search(
                r"^MemTotal:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1]),
            "load_before": list(os.getloadavg()), "load_after": None,
            "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS"),
            "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}


class Runner:
    def __init__(self, args, work, output):
        self.args, self.work, self.output = args, work, output
        self.token = uuid.uuid4().hex
        self.env = dict(os.environ, TURBO_LEAN_TELEMETRY="off", TURBO_LEAN_NO_WORKTREE_LINK="1",
                        TURBO_LEAN_NO_DAEMON="1", BENCH_CLIFV_RUN=self.token)
        # Always override inherited cache locations and remote worker routing.
        self.env.pop("TURBO_LEAN_REMOTE_HTTP", None)
        self.cache = work / "turbo-cache"
        self.env["TURBO_LEAN_HOME"] = str(self.cache)
        self.turbo = str(Path(shutil.which(args.turbo) or args.turbo).resolve())
        self.lake = shutil.which(args.lake)
        if not Path(self.turbo).is_file() or not self.lake:
            raise ValueError("lake and turbo-lean executables are required (or use --dry-run)")
        self.staging = Path(tempfile.mkdtemp(prefix=f"bench-clifv-{os.getuid()}-", dir="/dev/shm"))
        self.temp = work / "tmp"
        self.temp.mkdir()
        self.env.update(TURBO_LEAN_STAGING_DIR=str(self.staging), TMPDIR=str(self.temp))
        help_result = subprocess.run([self.turbo, "daemon", "stop", "--help"], env=self.env,
                                     capture_output=True, text=True)
        self.has_stop = help_result.returncode == 0 and "stop" in help_result.stdout.lower()

    def own_daemons(self):
        found = []
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                if entry.stat().st_uid != os.getuid():
                    continue
                env = (entry / "environ").read_bytes().split(b"\0")
                if f"BENCH_CLIFV_RUN={self.token}".encode() not in env:
                    continue
                argv = (entry / "cmdline").read_bytes().split(b"\0")
                name = Path(os.fsdecode(argv[0])).name
                if name == Path(self.turbo).name or name.startswith("turbo_zygote"):
                    found.append(int(entry.name))
            except (FileNotFoundError, PermissionError, ProcessLookupError):
                continue
        return found

    def stop_daemons(self):
        if self.has_stop:
            subprocess.run([self.turbo, "--cache-dir", str(self.cache), "daemon", "stop"],
                           cwd=self.work, env=self.env, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=30, check=True)
        # Older releases lack `daemon stop`; also reap any marked orphan workers.
        for sig in (signal.SIGTERM, signal.SIGKILL):
            for pid in self.own_daemons():
                try:
                    os.kill(pid, sig)
                except ProcessLookupError:
                    pass
            deadline = time.monotonic() + 3
            while self.own_daemons() and time.monotonic() < deadline:
                time.sleep(0.05)
        if self.own_daemons():
            raise RuntimeError("benchmark-owned turbo-lean processes survived cleanup")

    def command(self, arm):
        if arm == "stock":
            return [self.lake, "build"]
        return [self.turbo, "--cache-dir", str(self.cache), self.args.turbo_command,
                *(["FV"] if self.args.turbo_command == "check" else []), "--project-dir", "."]

    def run(self, arm, label, command=None):
        self.stop_daemons()
        cwd = self.work / arm
        log = self.output / "logs" / f"{label}-{arm}.log"
        timing = log.with_suffix(".time")
        command = command or self.command(arm)
        timed = ["/usr/bin/time", "-f", "%e %U %S %M", "-o", str(timing), "--", *command]
        print(f"{label}: {arm}", flush=True)
        before = list(os.getloadavg())
        with log.open("w") as stream:
            proc = subprocess.Popen(timed, cwd=cwd, env=self.env, stdout=stream, stderr=stream,
                                    start_new_session=True)
            try:
                rc = proc.wait(timeout=self.args.timeout or None)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                rc = 124
            except BaseException:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                raise
            finally:
                self.stop_daemons()
        numbers = timing.read_text().splitlines()[-1].split() if timing.exists() else []
        ok = len(numbers) == 4 and rc not in (124, 126, 127) and 0 <= rc < 128
        try:
            wall, user, system, rss = map(float, numbers)
            ok = ok and all(math.isfinite(v) and v >= 0 for v in (wall, user, system, rss)) and wall > 0
        except ValueError:
            wall = user = system = rss = 0
            ok = False
        return {"wall_s": wall, "user_s": user, "system_s": system, "cpu_s": user + system,
                "peak_rss_kib": int(rss), "exit_code": rc, "measurement_ok": ok,
                "command": command, "log": str(log.relative_to(self.output)),
                "load_before": before, "load_after": list(os.getloadavg())}

    def prepare(self):
        source = self.work / "source"
        subprocess.run(["git", "clone", "--no-checkout", self.args.repo, str(source)], check=True, env=self.env)
        sha = capture(["git", "rev-parse", "--verify", self.args.sha + "^{commit}"], source, self.env)
        subprocess.run(["git", "checkout", "--detach", sha], cwd=source, check=True, env=self.env)
        self.original = (source / EDIT_FILE).read_text()
        self.source_times = {}
        for scenario in self.args.scenarios:
            edited_source(self.original, scenario)
        for arm in ("stock", "turbo"):
            target = self.work / arm
            subprocess.run(["git", "clone", "--no-hardlinks", str(source), str(target)], check=True, env=self.env)
            subprocess.run(["git", "checkout", "--detach", sha], cwd=target, check=True, env=self.env)
            stat = (target / EDIT_FILE).stat()
            self.source_times[arm] = (stat.st_atime_ns, stat.st_mtime_ns)
        return sha, (source / "lean-toolchain").read_text().strip()

    def baseline(self):
        # Prime Lake in BOTH arms. Prime turbo's persistent CAS separately, untimed.
        for arm in ("stock", "turbo"):
            result = self.run(arm, "prime-lake", [self.lake, "build"])
            if result["exit_code"] or not result["measurement_ok"]:
                raise RuntimeError(f"baseline Lake build failed: {result['log']}")
        result = self.run("turbo", "prime-turbo")
        if result["exit_code"] or not result["measurement_ok"]:
            raise RuntimeError(f"baseline turbo warm-up failed: {result['log']}")
        for arm in ("stock", "turbo"):
            shutil.copytree(self.work / arm / ".lake", self.work / f"baseline-{arm}", symlinks=True)
        for name, path in self.cache_paths().items():
            if path.exists():
                shutil.copytree(path, self.work / f"baseline-{name}", symlinks=True)

    def cache_paths(self):
        return {"cache": self.cache, "staging": self.staging, "tmp": self.temp}

    def reset(self, arm, scenario):
        self.stop_daemons()
        target = self.work / arm
        # Restore tracked sources, then apply exactly one deterministic file edit.
        subprocess.run(["git", "reset", "--hard", "HEAD"], cwd=target, env=self.env,
                       check=True, stdout=subprocess.DEVNULL)
        os.utime(target / EDIT_FILE, ns=self.source_times[arm])
        shutil.rmtree(target / ".lake", ignore_errors=True)
        if scenario != "cold":
            shutil.copytree(self.work / f"baseline-{arm}", target / ".lake", symlinks=True)
        else:
            (target / ".lake").mkdir()
        if arm == "turbo":
            for name, path in self.cache_paths().items():
                shutil.rmtree(path, ignore_errors=True)
                baseline = self.work / f"baseline-{name}"
                if scenario != "cold" and baseline.exists():
                    shutil.copytree(baseline, path, symlinks=True)
                else:
                    path.mkdir(mode=0o700)
        if scenario in ("proof", "statement", "import"):
            (target / EDIT_FILE).write_text(edited_source(self.original, scenario))
        # Save exact input diff with the report, including the pristine (empty) diff.
        diff = capture(["git", "diff", "--", EDIT_FILE], target, self.env)
        (self.output / f"{scenario}-{arm}.patch").write_text(diff + "\n")


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="print a plan; no network, builds, or process cleanup")
    parser.add_argument("--scenarios", default=",".join(SCENARIOS), help="comma-separated cold,warm,proof,statement,import")
    parser.add_argument("--pairs", type=int, default=5)
    parser.add_argument("--sha", default="5018b95", help="clifv commit, not a branch or tag")
    parser.add_argument("--repo", default="https://github.com/eth-act/clifv.git")
    parser.add_argument("--turbo-command", choices=("build", "check"), default="build")
    parser.add_argument("--turbo", default="turbo-lean", help="executable built from --turbo-repo HEAD")
    parser.add_argument("--turbo-repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--work-dir", type=Path, default=Path("bench-clifv-work"))
    parser.add_argument("--output", type=Path, default=Path("bench-clifv-results"))
    parser.add_argument("--timeout", type=int, default=0, help="per-command seconds; 0 = unlimited")
    args = parser.parse_args(argv)
    args.scenarios = args.scenarios.split(",")
    if args.pairs < 1 or args.timeout < 0 or not re.fullmatch(r"[0-9a-fA-F]{7,40}", args.sha):
        parser.error("positive --pairs, nonnegative --timeout and a hexadecimal commit SHA are required")
    if len(set(args.scenarios)) != len(args.scenarios) or set(args.scenarios) - set(SCENARIOS):
        parser.error("--scenarios must contain unique names from " + ",".join(SCENARIOS))
    return args


def main(argv=None):
    args = parse_args(argv)
    if args.dry_run:
        print(json.dumps({"dry_run": True, "repo": args.repo, "clifv_sha": args.sha,
                          "pairs": args.pairs, "telemetry": "off", "turbo_command": args.turbo_command,
                          "scenarios": args.scenarios, "edit_file": EDIT_FILE,
                          "order": [a for _ in range(args.pairs) for a in ("stock", "turbo")],
                          "reset": "cold: empty .lake and CAS; otherwise restore independent baseline snapshots"}, indent=2))
        return 0
    work, output = args.work_dir.resolve(), args.output.resolve()
    if work.exists() or output.exists() or work in output.parents or output in work.parents:
        raise ValueError("use new, separate --work-dir and --output directories")
    if sys.platform != "linux" or not Path("/usr/bin/time").is_file():
        raise ValueError("Linux /proc and GNU /usr/bin/time are required")
    # Allocate only directories owned by this invocation; never delete a user's checkout.
    work.mkdir(parents=True)
    (output / "logs").mkdir(parents=True)
    runner = Runner(args, work, output)
    report = {"schema_version": 1, "status": "running", "telemetry": "off", "pairs_requested": args.pairs,
              "turbo_command": args.turbo_command, "machine": machine_info(), "scenarios": []}
    try:
        sha, toolchain = runner.prepare()
        turbo_env = runner.env
        turbo_sha = capture(["git", "rev-parse", "HEAD"], args.turbo_repo, turbo_env)
        if capture(["git", "status", "--porcelain", "--untracked-files=no"], args.turbo_repo, turbo_env):
            raise ValueError("--turbo-repo must have clean tracked files; build turbo from that HEAD")
        report["machine"].update({"clifv_sha": sha, "turbo_lean_sha": turbo_sha, "toolchain": toolchain,
            "turbo_binary": runner.turbo, "turbo_binary_sha256": hashlib.sha256(Path(runner.turbo).read_bytes()).hexdigest(),
            "turbo_version": capture([runner.turbo, "--version"], work, turbo_env),
            "lean_version": capture([runner.lake, "env", "lean", "--version"], work / "stock", turbo_env),
            "environment_overrides": {k: runner.env[k] for k in ("TURBO_LEAN_TELEMETRY", "TURBO_LEAN_HOME",
                "TURBO_LEAN_STAGING_DIR", "TURBO_LEAN_NO_DAEMON", "TURBO_LEAN_NO_WORKTREE_LINK", "TMPDIR")},
            "daemon_stop": "command + owned-worker cleanup" if runner.has_stop else "owned-process cleanup"})
        if any(s != "cold" for s in args.scenarios):
            runner.baseline()
        for scenario in args.scenarios:
            entry = {"name": scenario, "pairs": []}
            report["scenarios"].append(entry)
            for index in range(1, args.pairs + 1):
                results = {}
                for arm in ("stock", "turbo"):
                    runner.reset(arm, scenario)
                    results[arm] = runner.run(arm, f"{scenario}-{index}")
                entry["pairs"].append(pair_record(index, **results))
                entry["summary"] = summarize(entry["pairs"])
                report["machine"]["load_after"] = list(os.getloadavg())
                write_report(report, output)
        report["status"] = "complete"
    finally:
        runner.stop_daemons()
        shutil.rmtree(runner.staging)
        report["machine"]["load_after"] = list(os.getloadavg())
        if report["status"] != "complete":
            report["status"] = "aborted"
        # An interrupted pair never enters the report as a valid pair.
        report["scenarios"] = [s for s in report["scenarios"] if s["pairs"]]
        write_report(report, output)
    print(f"Reports: {output / 'results.json'} and {output / 'results.md'}")
    return 2 if any(p["parity"] == "INVALID" for s in report["scenarios"] for p in s["pairs"]) else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"bench_clifv: {error}", file=sys.stderr)
        sys.exit(1)
