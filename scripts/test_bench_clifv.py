#!/usr/bin/env python3
"""No Lean, clifv download, network, or turbo binary needed."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import jsonschema
import bench_clifv as bench

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = json.loads((ROOT / "scripts/bench_clifv.schema.json").read_text())


def measurement(wall, cpu, rss, rc=0, ok=True):
    return {"wall_s": wall, "user_s": cpu, "system_s": 0.0, "cpu_s": cpu,
            "peak_rss_kib": rss, "exit_code": rc, "measurement_ok": ok,
            "command": ["fake"], "log": "fake.log", "load_before": [0, 0, 0], "load_after": [0, 0, 0]}


def fake_report():
    pairs = [bench.pair_record(i + 1, measurement(a, a / 2, 1000), measurement(b, b / 2, 900))
             for i, (a, b) in enumerate([(10.0, 5.0), (10.2, 4.9)])]
    machine = {"hostname": "FAKE", "platform": "FAKE", "nproc": 2, "mem_total_kib": 1024,
               "load_before": [0, 0, 0], "load_after": [0, 0, 0], "LEAN_NUM_THREADS": None,
               "started_utc": "2000-01-01T00:00:00+00:00", "clifv_sha": "0" * 40,
               "turbo_lean_sha": "1" * 40, "toolchain": "FAKE", "turbo_binary": "fake",
               "turbo_binary_sha256": "2" * 64, "turbo_version": "FAKE", "lean_version": "FAKE",
               "daemon_stop": "FAKE", "environment_overrides": {"TURBO_LEAN_TELEMETRY": "off"}}
    return {"schema_version": 1, "status": "complete", "telemetry": "off", "pairs_requested": 2,
            "turbo_command": "build", "machine": machine,
            "scenarios": [{"name": "warm", "pairs": pairs}]}


class Reports(unittest.TestCase):
    def test_fake_two_pair_schema_and_bootstrap(self):
        report = fake_report()
        with tempfile.TemporaryDirectory() as directory:
            bench.write_report(report, Path(directory))
            stored = json.loads((Path(directory) / "results.json").read_text())
            jsonschema.Draft202012Validator(SCHEMA).validate(stored)
            ratio = stored["scenarios"][0]["summary"]["paired_wall_ratio"]
            self.assertEqual(ratio["mean"], (10 / 5 + 10.2 / 4.9) / 2)
            self.assertEqual(ratio["bootstrap_95_ci"], [2, 10.2 / 4.9])
            self.assertNotEqual(ratio["mean"], 10.1 / 4.95)  # not a ratio of unpaired means
            self.assertEqual(len(stored["scenarios"][0]["pairs"]), 2)
            # The CI artifact is an actual two-pair JSON file, independently validated.
            artifact = os.environ.get("BENCH_SELF_TEST_OUTPUT")
            if artifact:
                shutil.copytree(directory, artifact, dirs_exist_ok=True)

    def test_parity_is_verdict_not_identical_exit_code(self):
        self.assertEqual(bench.pair_record(1, measurement(1, 1, 1, 1), measurement(1, 1, 1, 2))["parity"], "FAIL")
        self.assertEqual(bench.pair_record(1, measurement(1, 1, 1), measurement(1, 1, 1, 1))["parity"], "INVALID")
        self.assertEqual(bench.pair_record(1, measurement(1, 1, 1, 1, False), measurement(1, 1, 1, 1))["parity"], "INVALID")

    def test_timing_parser_rejects_missing_corrupt_signal_and_timeout(self):
        good = "Command exited with non-zero status 1\n0.25 0.10 0.05 4096\n"
        parsed = bench.parse_timing(good, 1)
        self.assertTrue(parsed["measurement_ok"])
        self.assertAlmostEqual(parsed["cpu_s"], 0.15)
        for content, code in (("", 0), ("bad", 0), ("nan 1 1 1", 0), ("1 -1 1 1", 0),
                              (good, 124), (good, 127), (good, 137), (good, -9)):
            self.assertFalse(bench.parse_timing(content, code)["measurement_ok"])

    def test_schema_rejects_missing_raw_measurement(self):
        report = fake_report()
        with tempfile.TemporaryDirectory() as directory:
            bench.write_report(report, Path(directory))
        del report["scenarios"][0]["pairs"][0]["stock"]["peak_rss_kib"]
        with self.assertRaises(jsonschema.ValidationError):
            jsonschema.validate(report, SCHEMA)

    def test_ratio_gate_and_global_invalid(self):
        for cause in ("wall", "cpu", "rss", "failure", "invalid", "zero", "single", "incomplete"):
            with self.subTest(cause=cause), tempfile.TemporaryDirectory() as directory:
                report = fake_report()
                pairs = report["scenarios"][0]["pairs"]
                if cause in ("wall", "cpu", "rss"):
                    pairs[1]["stock"][{"wall": "wall_s", "cpu": "cpu_s", "rss": "peak_rss_kib"}[cause]] *= 3
                elif cause == "failure":
                    for pair in pairs:
                        for arm in ("stock", "turbo"):
                            pair[arm]["exit_code"] = 1
                        pair["parity"] = "FAIL"
                elif cause == "invalid":
                    other = copy.deepcopy(report["scenarios"][0])
                    other["name"] = "proof"
                    other["pairs"][0]["turbo"]["exit_code"] = 1
                    other["pairs"][0]["parity"] = "INVALID"
                    report["scenarios"].append(other)
                elif cause == "zero":
                    for pair in pairs:
                        pair["turbo"]["cpu_s"] = 0
                elif cause == "single":
                    pairs.pop()
                else:
                    report["status"] = "aborted"
                bench.write_report(report, Path(directory))
                jsonschema.validate(report, SCHEMA)
                self.assertIsNone(report["scenarios"][0]["summary"]["paired_wall_ratio"])
                self.assertFalse(report["scenarios"][0]["summary"]["speedup_claim_allowed"])
                self.assertNotIn("×", (Path(directory) / "results.md").read_text())

    def test_edits_and_anchor_guard(self):
        source = "import Init\n" + bench.THEOREM + "\n"
        self.assertIn("simpa only", bench.edited_source(source, "proof"))
        statement = bench.edited_source(source, "statement")
        self.assertIn("5 ((), 7) = ((), 12)", statement)
        self.assertIn("rw [iterN_stepC, countIn_true]", statement)
        self.assertEqual(bench.edited_source(source, "import"), "import Init\n" + source)
        with self.assertRaises(ValueError):
            bench.edited_source(source.replace("iterN_stepC_id", "renamed"), "proof")

    def test_dry_run_needs_no_tools_or_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([str(ROOT / "scripts/bench_clifv.sh"), "--dry-run", "--pairs", "2",
                                     "--scenarios", "warm,proof", "--turbo", "/missing"],
                                    cwd=directory, text=True, capture_output=True, check=True)
            plan = json.loads(result.stdout)
            self.assertEqual(plan["order"], ["stock", "turbo", "stock", "turbo"])
            self.assertEqual(plan["scenarios"], ["warm", "proof"])
            self.assertEqual(list(Path(directory).iterdir()), [])


FAKE_TOOL = '''#!/usr/bin/env python3
import hashlib, json, os, pathlib, sys, time
args = sys.argv[1:]
if "--help" in args:
    if os.environ.get("FAKE_STOP_SUPPORTED") == "1":
        print("daemon stop")
        sys.exit(0)
    sys.exit(2)
if "--version" in args:
    print("fake version")
    sys.exit(0)
if "daemon" in args:
    assert os.environ["TURBO_LEAN_TELEMETRY"] == "off"
    sys.exit(0)
assert os.environ["TURBO_LEAN_TELEMETRY"] == "off"
assert os.environ["TURBO_LEAN_NO_DAEMON"] == "1"
p = pathlib.Path
arm = p.cwd().name
source = p("FV/E2E/RegLevelCountIWitness.lean")
lake = p(".lake/state")
cache = p(os.environ["TURBO_LEAN_HOME"]) / "state"
staging = p(os.environ["TURBO_LEAN_STAGING_DIR"]) / "state"
temp = p(os.environ["TMPDIR"]) / "state"
state = lambda f: f.read_text() if f.exists() else None
is_turbo = "turbo" in p(sys.argv[0]).name
record = {"arm": arm, "is_turbo": is_turbo, "source": source.read_text(),
          "mtime": source.stat().st_mtime_ns, "lake": state(lake),
          "cache": state(cache), "staging": state(staging), "temp": state(temp), "args": args}
with open(os.environ["FAKE_TRACE"], "a") as stream:
    stream.write(json.dumps(record) + "\\n")
for f in ([lake, cache, staging, temp] if is_turbo else [lake]):
    f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text("primed" if state(f) is None else "changed")
# Enough work for nonzero GNU time wall/CPU observations, without Lean.
start = time.process_time()
while time.process_time() - start < 0.025:
    hashlib.sha256(b"fake fixture").digest()
time.sleep(0.025)
if is_turbo and os.environ.get("FAKE_FAIL_TURBO") == "1":
    sys.exit(1)
'''


class Integration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        source = self.repo / bench.EDIT_FILE
        source.parent.mkdir(parents=True)
        source.write_text("import Init\n" + bench.THEOREM + "\n")
        (self.repo / "lean-toolchain").write_text("fake-toolchain\n")
        for args in (["init", "-q"], ["add", "."],
                     ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"]):
            subprocess.run(["git", *args], cwd=self.repo, check=True)
        self.sha = bench.capture(["git", "rev-parse", "HEAD"], self.repo)
        self.env = dict(os.environ, FAKE_TRACE=str(self.root / "trace"))
        for name in ("fake-lake", "fake-turbo"):
            tool = self.root / name
            tool.write_text(FAKE_TOOL)
            tool.chmod(0o755)

    def run_fixture(self, scenarios, command="build", fail=False):
        work, output = self.root / "work", self.root / "output"
        cmd = [str(ROOT / "scripts/bench_clifv.sh"), "--pairs", "2", "--repo", str(self.repo),
               "--sha", self.sha, "--turbo-repo", str(self.repo), "--turbo", str(self.root / "fake-turbo"),
               "--lake", str(self.root / "fake-lake"), "--work-dir", str(work), "--output", str(output),
               "--scenarios", scenarios, "--turbo-command", command]
        if fail:
            self.env["FAKE_FAIL_TURBO"] = "1"
        result = subprocess.run(cmd, env=self.env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 2 if fail else 0, result.stdout + result.stderr)
        report = json.loads((output / "results.json").read_text())
        jsonschema.validate(report, SCHEMA)
        self.assertEqual(report["machine"]["clifv_sha"], self.sha)
        self.assertEqual(report["status"], "complete")
        self.assertFalse(Path(report["machine"]["environment_overrides"]["TURBO_LEAN_STAGING_DIR"]).exists())
        events = [json.loads(line) for line in (self.root / "trace").read_text().splitlines()]
        return report, events

    def test_all_scenarios_restore_cache_and_source_in_any_order(self):
        report, events = self.run_fixture("cold,proof,warm,statement,import")
        self.assertEqual(len(events), 3 + 5 * 4)  # three untimed primes
        timed = events[3:]
        self.assertEqual([e["arm"] for e in timed], ["stock", "turbo"] * 10)
        for index, scenario in enumerate(("cold", "proof", "warm", "statement", "import")):
            group = timed[index * 4:index * 4 + 4]
            for i in (0, 1):
                self.assertEqual(group[i]["source"], group[i + 2]["source"])
                self.assertEqual(group[i]["lake"], group[i + 2]["lake"])
            self.assertEqual(group[0]["source"], group[1]["source"])
            if scenario == "cold":
                self.assertTrue(all(e["lake"] is None for e in group))
                self.assertTrue(all(group[i][k] is None for i in (1, 3) for k in ("cache", "staging", "temp")))
            else:
                self.assertEqual(group[0]["lake"], "primed")
                self.assertEqual(group[1]["lake"], "changed")
                self.assertTrue(all(group[i][k] == "primed" for i in (1, 3) for k in ("cache", "staging", "temp")))
            if scenario == "warm":
                self.assertEqual(group[0]["mtime"], events[0]["mtime"])
                self.assertEqual(group[1]["mtime"], events[1]["mtime"])
        self.assertEqual([s["name"] for s in report["scenarios"]], ["cold", "proof", "warm", "statement", "import"])

    def test_check_mode_and_daemon_stop_capability(self):
        self.env["FAKE_STOP_SUPPORTED"] = "1"
        report, events = self.run_fixture("cold", "check")
        self.assertEqual(len(events), 4)  # cold-only does not prime
        self.assertTrue(all("check" in e["args"] and "FV" in e["args"] for e in events if e["is_turbo"]))
        self.assertIn("command", report["machine"]["daemon_stop"])

    def test_invalid_experiment_exit_status(self):
        report, _ = self.run_fixture("cold", fail=True)
        self.assertTrue(all(p["parity"] == "INVALID" for p in report["scenarios"][0]["pairs"]))

    def test_cleanup_targets_only_marked_owned_workers(self):
        args = bench.parse_args(["--turbo", str(self.root / "fake-turbo"), "--lake", str(self.root / "fake-lake")])
        work = self.root / "cleanup-work"
        work.mkdir()
        runner = bench.Runner(args, work, self.root)
        self.addCleanup(shutil.rmtree, runner.staging, True)
        worker = self.root / "turbo_zygote_fixture"
        shutil.copyfile("/bin/sleep", worker)
        worker.chmod(0o755)
        marked = subprocess.Popen([str(worker), "30"], env=runner.env)
        unrelated = subprocess.Popen([str(worker), "30"])
        try:
            self.assertIn(marked.pid, runner.own_daemons())
            self.assertNotIn(unrelated.pid, runner.own_daemons())
            runner.stop_daemons()
            self.assertIsNotNone(marked.poll())
            self.assertIsNone(unrelated.poll())
        finally:
            unrelated.kill()
            unrelated.wait()
            if marked.poll() is None:
                marked.kill()
            marked.wait()


if __name__ == "__main__":
    unittest.main()
