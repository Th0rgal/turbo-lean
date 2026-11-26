#!/usr/bin/env python3
"""Contract tests for `scripts/bench_build_loop.py` (build-shaped warm loop).

Run: python3 scripts/test_bench_build_loop.py
No Lean toolchain or turbo-lean build required: the end-to-end cases drive the
script with a stub binary that emulates `build --json` (a cold seeded build,
then warm cache hits). The stub also emulates a binary from before the G2b
warm replay was deleted: it replays when TURBO_LEAN_WARM_CAS_REPLAY=1 reaches
it and TURBO_LEAN_NO_WARM_CAS_REPLAY=1 does not, which the script must never
let happen.

The timeout test makes the script signal a process group it started, and its
cleanup signals one `sleep` the stub started. On a shared machine run the file
inside an isolated PID namespace: `unshare -r -m -p -f --mount-proc bash -c
'python3 scripts/test_bench_build_loop.py'`.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parent / "bench_build_loop.py"
RETIRED = ("TURBO_LEAN_WARM_CAS_REPLAY", "TURBO_LEAN_NO_WARM_CAS_REPLAY")


def load_script():
    spec = importlib.util.spec_from_file_location("bench_build_loop", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


mod = load_script()

STUB = r'''#!/usr/bin/env python3
import json, os, sys, time
args = sys.argv[1:]
proj = args[args.index("--project-dir") + 1]
seed = "--seed-shards" in args
log = os.environ.get("FAKE_LOG")
if log:
    with open(log, "a") as fh:
        fh.write(json.dumps({
            "seed": seed, "build": "build" in args,
            "warm": os.environ.get("TURBO_LEAN_WARM_CAS_REPLAY"),
            "no_warm": os.environ.get("TURBO_LEAN_NO_WARM_CAS_REPLAY"),
            "no_daemon": os.environ.get("TURBO_LEAN_NO_DAEMON"),
            "telemetry": os.environ.get("TURBO_LEAN_TELEMETRY"),
            "home_set": bool(os.environ.get("TURBO_LEAN_HOME"))}) + "\n")
theorems = 0
for dirpath, _dirs, names in os.walk(proj):
    for name in names:
        if name.endswith(".lean"):
            with open(os.path.join(dirpath, name)) as fh:
                theorems += sum(1 for line in fh if line.startswith("theorem "))
time.sleep(float(os.environ.get("FAKE_SLEEP_MS", "5")) / 1000)
if log and os.environ.get("FAKE_FAIL_CALL"):
    with open(log) as fh:
        call_number = sum(1 for _ in fh)
    if call_number == int(os.environ["FAKE_FAIL_CALL"]):
        sys.stderr.write("fake failure\n")
        if os.environ.get("FAKE_FAIL_SHOW_HOME"):
            sys.stderr.write("home was " + os.environ["TURBO_LEAN_HOME"] + "\n")
            sys.stderr.write("binary was " + sys.argv[0] + "\n")
        sys.exit(3)
if not seed and os.environ.get("FAKE_HANG_PID_FILE"):
    # A warm call that hangs with a child of its own holding the output pipe.
    import subprocess
    child = subprocess.Popen(["sleep", "120"])
    with open(os.environ["FAKE_HANG_PID_FILE"], "w") as fh:
        fh.write(str(child.pid))
    sys.stderr.write("hung call\n")
    sys.stderr.flush()
    time.sleep(120)
if seed:
    # Like the real tool's closure-snapshot store: read-only directories under
    # TURBO_LEAN_HOME, which a plain rmtree cannot empty.
    snap = os.path.join(os.environ["TURBO_LEAN_HOME"], "closure-realm",
                        "closure-snapshots", "d0", "BenchFixture")
    os.makedirs(snap)
    with open(os.path.join(snap, "M0.ilean"), "w") as fh:
        fh.write("x")
    os.chmod(os.path.join(snap, "M0.ilean"), 0o444)
    os.chmod(snap, 0o500)
    os.chmod(os.path.dirname(snap), 0o500)
    out = {"status": "built", "shards_seeded": int(os.environ.get("FAKE_SEEDED", theorems)),
           "cas_expr_replayed": 0, "modules_total": 3, "modules_compiled": 3,
           "artifacts_stored": 7, "materialized_files": 7, "elapsed_ms": 40}
else:
    # A pre-deletion binary replays on a warm hit when the opt-in reaches it and
    # the force-off switch does not.
    replays = (os.environ.get("TURBO_LEAN_WARM_CAS_REPLAY") == "1"
               and os.environ.get("TURBO_LEAN_NO_WARM_CAS_REPLAY") != "1")
    out = {"status": os.environ.get("FAKE_WARM_STATUS", "cache_hit"),
           "cas_expr_replayed": (int(os.environ["FAKE_REPLAYED"])
                                 if os.environ.get("FAKE_REPLAYED")
                                 else (theorems if replays else 0)),
           "materialized_files": 7, "elapsed_ms": 12}
print(json.dumps(out, indent=2))
'''


def make_stub(root: Path) -> Path:
    stub = root / "fake-turbo-lean"
    stub.write_text(STUB)
    stub.chmod(0o755)
    return stub


def make_fake_lean(root: Path) -> Path:
    bin_dir = root / "fake-bin"
    bin_dir.mkdir(exist_ok=True)
    lean = bin_dir / "lean"
    lean.write_text("#!/bin/sh\nprintf 'Lean (version 4.35.0, fake)\\n'\n")
    lean.chmod(0o755)
    return bin_dir


def process_is_alive(pid: int) -> bool:
    """True while /proc lists the pid as anything but a zombie."""
    try:
        text = Path(f"/proc/{pid}/stat").read_text()
    except OSError:
        return False
    return text.rpartition(") ")[2].split()[0] not in ("Z", "X")


def stop_own_child(pid: int) -> None:
    """Cleanup for a `sleep` this test's stub started and the script left running."""
    try:
        if Path(f"/proc/{pid}/comm").read_text().strip() == "sleep" and process_is_alive(pid):
            os.kill(pid, signal.SIGKILL)
    except OSError:
        pass


def clean_env(**extra):
    env = {k: v for k, v in os.environ.items() if k not in RETIRED}
    env.update(extra)
    return env


def run_script(root: Path, extra=(), env_extra=None, trials=4, warmup=1, timeout=300):
    stub = make_stub(root)
    bin_dir = make_fake_lean(root)
    scratch = root / "scratch"
    scratch.mkdir(exist_ok=True)
    env = clean_env(PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""),
                    FAKE_LOG=str(root / "calls.jsonl"))
    env.update(env_extra or {})
    cmd = [sys.executable, str(SCRIPT), "--turbo-lean-bin", str(stub),
           "--trials", str(trials), "--warmup", str(warmup), "--modules", "2",
           "--theorems-per-module", "3", "--allow-busy-node",
           "--scratch-dir", str(scratch), "--out", str(root / "out.json")] + list(extra)
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)


def read_calls(root: Path):
    p = root / "calls.jsonl"
    if not p.is_file():
        return []
    return [json.loads(line) for line in p.read_text().splitlines() if line.strip()]


class FixtureTests(unittest.TestCase):
    def test_fixture_shape_and_one_clean_theorem_per_shard(self):
        files = mod.fixture_files(3, 4, "leanprover/lean4:v4.35.0")
        self.assertEqual(set(files), {
            "lean-toolchain", "lakefile.toml", "BenchFixture.lean",
            "BenchFixture/M0.lean", "BenchFixture/M1.lean", "BenchFixture/M2.lean"})
        self.assertEqual(files["lean-toolchain"], "leanprover/lean4:v4.35.0\n")
        self.assertIn('[[lean_lib]]\nname = "BenchFixture"\n', files["lakefile.toml"])
        self.assertEqual(files["BenchFixture.lean"],
                         "import BenchFixture.M0\nimport BenchFixture.M1\nimport BenchFixture.M2\n")
        bodies = "".join(files[f"BenchFixture/M{m}.lean"] for m in range(3))
        decls = re.findall(r"^theorem (\S+) (.*) := by omega$", bodies, re.M)
        self.assertEqual(len(decls), 12)
        # Distinct names and distinct statements: twelve distinct shard keys.
        self.assertEqual(len({name for name, _ in decls}), 12)
        self.assertEqual(len({stmt for _, stmt in decls}), 12)
        self.assertNotIn("sorry", bodies)
        # Independent modules: the cold build compiles them in parallel.
        for m in range(3):
            self.assertNotIn("import", files[f"BenchFixture/M{m}.lean"])

    def test_fixture_digest_is_deterministic_and_content_bound(self):
        a = mod.fixture_digest(mod.fixture_files(2, 3, "tc"))
        self.assertEqual(a, mod.fixture_digest(mod.fixture_files(2, 3, "tc")))
        self.assertNotEqual(a, mod.fixture_digest(mod.fixture_files(2, 4, "tc")))
        self.assertNotEqual(a, mod.fixture_digest(mod.fixture_files(2, 3, "tc2")))

    def test_remove_tree_clears_read_only_dirs_and_never_follows_a_symlink(self):
        with tempfile.TemporaryDirectory() as td:
            base = Path(td).resolve()
            outside = base / "outside"
            outside.mkdir()
            (outside / "keep.txt").write_text("k")
            outside.chmod(0o555)
            root = base / "scratch-root"
            store = root / "home" / "closure-realm" / "d0"
            store.mkdir(parents=True)
            (store / "x.ilean").write_text("x")
            store.chmod(0o500)
            store.parent.chmod(0o500)
            (root / "link").symlink_to(outside, target_is_directory=True)
            try:
                mod.remove_tree(root)
                self.assertFalse(root.exists())
                self.assertEqual(stat.S_IMODE(outside.stat().st_mode), 0o555)
                self.assertEqual((outside / "keep.txt").read_text(), "k")
            finally:
                outside.chmod(0o755)

    def test_write_fixture_round_trips(self):
        files = mod.fixture_files(2, 2, "tc")
        with tempfile.TemporaryDirectory() as td:
            mod.write_fixture(Path(td), files)
            for rel, text in files.items():
                self.assertEqual((Path(td) / rel).read_text(), text)


class StatisticsTests(unittest.TestCase):
    def test_series_stats_quartiles_inclusive(self):
        s = mod.series_stats([10.0, 20.0, 30.0, 40.0, 50.0])
        self.assertEqual((s["n"], s["median_ms"], s["q1_ms"], s["q3_ms"], s["iqr_ms"]),
                         (5, 30.0, 20.0, 40.0, 20.0))
        self.assertEqual(s["rel_spread"], 1.3333)
        self.assertIsNone(mod.series_stats([7.0])["iqr_ms"])
        self.assertIsNone(mod.series_stats([])["median_ms"])


class ExpectationTests(unittest.TestCase):
    OK = {"exit_code": 0, "json": {"status": "cache_hit", "cas_expr_replayed": 0}}

    def test_a_warm_call_must_be_a_healthy_cache_hit(self):
        self.assertIsNone(mod.trial_problem(self.OK))
        self.assertIn("expected 'cache_hit'",
                      mod.trial_problem(dict(self.OK, json={"status": "built"})))
        self.assertEqual(mod.trial_problem({"exit_code": 3, "json": None, "stderr": "boom\n"}),
                         "exit 3: boom")
        self.assertEqual(mod.trial_problem({"exit_code": 0, "json": None}),
                         "no JSON object on stdout")

    def test_cold_build_must_seed_one_receipt_per_theorem(self):
        ok = {"exit_code": 0, "json": {"status": "built", "shards_seeded": 12}}
        self.assertIsNone(mod.cold_problem(ok, 12))
        self.assertIn("expected 12",
                      mod.cold_problem(dict(ok, json={"status": "built", "shards_seeded": 11}), 12))
        self.assertIn("expected 'built'",
                      mod.cold_problem(dict(ok, json={"status": "cache_hit",
                                                      "shards_seeded": 12}), 12))

    def test_binary_is_recorded_relative_or_by_name(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            b = root / "target" / "release" / "turbo-lean"
            self.assertEqual(mod.binary_record(b, str(root), "s")["path"],
                             "target/release/turbo-lean")
            self.assertEqual(mod.binary_record(b, None, "s")["path"], "turbo-lean")
            self.assertEqual(mod.binary_record(b, str(root / "elsewhere"), "s")["path"],
                             "turbo-lean")

    def test_child_env_removes_the_opt_in_and_forces_the_replay_off(self):
        scratch = Path("/nonexistent/scratch")
        with mock.patch.dict(os.environ, {RETIRED[0]: "1", RETIRED[1]: "0",
                                          "TURBO_LEAN_NO_DAEMON": "0"}):
            env = mod.child_env(scratch)
        # A binary from before the deletion must not replay: the opt-in is gone and
        # the force-off switch is set, not merely dropped.
        self.assertNotIn(RETIRED[0], env)
        self.assertEqual(env[RETIRED[1]], "1")
        self.assertEqual((env["TURBO_LEAN_NO_DAEMON"], env["TURBO_LEAN_TELEMETRY"]), ("1", "off"))
        self.assertEqual(env["TURBO_LEAN_HOME"], str(scratch / "home"))

    def test_child_env_is_derived_from_the_recorded_child_common(self):
        scratch = Path("/nonexistent/scratch")
        extra = {"TURBO_LEAN_EXTRA_PROBE": "<scratch>/probe", "TURBO_LEAN_PLAIN_PROBE": "7"}
        with mock.patch.dict(mod.CHILD_COMMON, extra):
            env = mod.child_env(scratch)
            for key, value in mod.CHILD_COMMON.items():
                self.assertEqual(env[key], value.replace("<scratch>", str(scratch)), key)
        self.assertEqual(env["TURBO_LEAN_EXTRA_PROBE"], "/nonexistent/scratch/probe")
        self.assertEqual(env["TURBO_LEAN_PLAIN_PROBE"], "7")

    def test_a_warm_call_that_replayed_is_a_trial_problem(self):
        ok = {"exit_code": 0, "json": {"status": "cache_hit", "cas_expr_replayed": 0}}
        self.assertIsNone(mod.trial_problem(ok))
        self.assertIsNone(mod.trial_problem(
            {"exit_code": 0, "json": {"status": "cache_hit"}}))
        self.assertIsNone(mod.trial_problem(
            {"exit_code": 0, "json": {"status": "cache_hit", "cas_expr_replay_mode": "off"}}))
        replayed = mod.trial_problem(
            {"exit_code": 0, "json": {"status": "cache_hit", "cas_expr_replayed": 200}})
        self.assertIn("replay", replayed)
        self.assertIn("200", replayed)
        moded = mod.trial_problem(
            {"exit_code": 0, "json": {"status": "cache_hit", "cas_expr_replayed": 0,
                                      "cas_expr_replay_mode": "warm_opt_in"}})
        self.assertIn("warm_opt_in", moded)

    def test_failure_heads_name_the_scratch_root_by_placeholder(self):
        roots = mod.path_roots(Path("/run/x/build-loop-ab12"), Path("/opt/tl/bin/turbo-lean"),
                               "/opt/gitbin/git")
        r = {"exit_code": 3, "json": None,
             "stderr": "cannot open /run/x/build-loop-ab12/home/db via /opt/tl/bin/turbo-lean"
                       " and /opt/gitbin/git\n"}
        want = "exit 3: cannot open <scratch>/home/db via <bin-dir>/turbo-lean and <git-dir>/git"
        self.assertEqual(mod.trial_problem(r, roots), want)
        self.assertEqual(mod.cold_problem(r, 6, roots), want)


class CommittedArtifactTests(unittest.TestCase):
    def test_the_g2b_artifact_is_the_schema_1_on_off_run_at_0a593169(self):
        # The artifact is the evidence behind a deleted feature; the current script
        # writes schema 2 with no sides, so a rerun pointed at it would replace it.
        res = json.loads((SCRIPT.parent / "bench_build_loop_g2b.json").read_text())
        self.assertEqual(res["schema_version"], 1)
        self.assertIn("on", res["sides"])
        self.assertIn("off", res["sides"])
        self.assertTrue(res["turbo_lean_commit"].startswith("0a593169"),
                        res["turbo_lean_commit"])


class EndToEndTests(unittest.TestCase):
    def test_measures_warm_cache_hit_builds(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            text = (root / "out.json").read_text()
            res = json.loads(text)
            self.assertEqual((res["schema_version"], res["kind"]), (2, "build_loop_results"))
            for gone in ("leaf", "sides", "delta"):
                self.assertNotIn(gone, res)
            self.assertEqual(res["verdict"], {"verdict": "measured", "problems": []})
            self.assertEqual((res["cold"]["status"], res["cold"]["shards_seeded"],
                              res["cold"]["problem"]), ("built", 6, None))
            self.assertEqual(res["fixture"]["theorems"], 6)
            warm = res["warm"]
            self.assertEqual((warm["trials"], warm["failed_trials"]), (4, 0))
            self.assertIsNotNone(warm["iqr_ms"])
            self.assertEqual(warm["tool_elapsed_ms"]["n"], 4)
            self.assertEqual(warm["materialized_files_observed"], [7])
            self.assertNotIn("coverage_ratio_min", warm)
            self.assertEqual([s["call"] for s in res["sequence"]], [0, 1, 2, 3, 4])
            self.assertEqual([s["measured"] for s in res["sequence"]], [False] + [True] * 4)
            # The cold build seeds; every warm call omits --seed-shards; no call sees
            # a retired switch; no daemon and no telemetry anywhere.
            calls = read_calls(root)
            self.assertEqual(len(calls), 6)
            self.assertTrue(calls[0]["seed"])
            for call in calls[1:]:
                self.assertFalse(call["seed"])
            for call in calls:
                self.assertTrue(call["build"])
                self.assertEqual((call["warm"], call["no_warm"]), (None, "1"))
                self.assertEqual((call["no_daemon"], call["telemetry"]), ("1", "off"))
                self.assertTrue(call["home_set"])
            # The scratch root is removed, and the artifact carries no path of it.
            self.assertEqual(list((root / "scratch").iterdir()), [])
            self.assertNotIn(str(root), text)
            # Relative to an enclosing repository when there is one, else by name.
            bin_path = res["turbo_lean_binary"]["path"]
            self.assertFalse(os.path.isabs(bin_path), bin_path)
            self.assertTrue(bin_path.endswith("fake-turbo-lean"), bin_path)
            self.assertEqual(res["settings"]["argv_warm"][-3:],
                             ["build", "--project-dir", "<scratch>/fixture"])
            self.assertEqual(res["settings"]["argv_cold"][-1], "--seed-shards")
            self.assertEqual(res["settings"]["child_removed"], [RETIRED[0]])
            self.assertEqual(res["settings"]["child_common"][RETIRED[1]], "1")
            self.assertIn("BUILD LOOP: warm cache-hit build", proc.stdout)

    def test_exported_retired_switches_never_reach_a_call(self):
        # The stub replays like a pre-deletion binary when the opt-in reaches it and
        # the force-off switch does not; the script drops the opt-in and sets the
        # force-off, so every call still measures a plain warm build.
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={RETIRED[0]: "1", RETIRED[1]: "0"})
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            calls = read_calls(root)
            self.assertEqual(len(calls), 6)
            for call in calls:
                self.assertEqual((call["warm"], call["no_warm"]), (None, "1"))

    def test_a_replaying_binary_fails_the_run(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_REPLAYED": "6"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            self.assertEqual(res["verdict"]["verdict"], "measurement_failed")
            self.assertTrue(all("replay" in p for p in res["verdict"]["problems"]),
                            res["verdict"]["problems"])

    def test_a_failure_text_names_the_scratch_root_only_by_placeholder(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_FAIL_CALL": "2",
                                               "FAKE_FAIL_SHOW_HOME": "1"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            text = (root / "out.json").read_text()
            self.assertIn("home was <scratch>/home", text)
            self.assertIn("binary was <bin-dir>/fake-turbo-lean", text)
            # A failing call's excerpt carries no host path at all.
            for host_path in {str(root), os.path.realpath(str(root))}:
                self.assertNotIn(host_path, text)

    def test_a_timed_out_call_takes_its_children_with_it(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            pid_file = root / "child.pid"
            try:
                # Without a process group kill the hung call's child keeps the output
                # pipe open and the run waits for it.
                proc = run_script(root, extra=["--build-timeout-s", "1"], trials=1,
                                  warmup=0, timeout=60,
                                  env_extra={"FAKE_HANG_PID_FILE": str(pid_file)})
                self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
                res = json.loads((root / "out.json").read_text())
                self.assertIn("timeout after 1s", " ".join(res["verdict"]["problems"]))
                self.assertIn("hung call", " ".join(res["verdict"]["problems"]))
                pid = int(pid_file.read_text())
                for _ in range(100):
                    if not process_is_alive(pid):
                        break
                    time.sleep(0.05)
                self.assertFalse(process_is_alive(pid), "the hung call's child is still running")
            finally:
                if pid_file.is_file():
                    stop_own_child(int(pid_file.read_text()))

    def test_a_warm_call_that_is_not_a_cache_hit_fails_the_run(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_WARM_STATUS": "built"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            v = res["verdict"]
            self.assertEqual(v["verdict"], "measurement_failed")
            self.assertEqual(v["problems"], [
                f"call {c}: status 'built', expected 'cache_hit'" for c in (1, 2, 3, 4)
            ] + ["warmup call 0: status 'built', expected 'cache_hit'"])
            # `trials` counts the healthy calls (the check-loop bench's mode-result shape).
            self.assertEqual((res["warm"]["trials"], res["warm"]["failed_trials"]), (0, 4))
            self.assertIsNone(res["warm"]["median_ms"])
            self.assertIn("VERDICT: measurement_failed", proc.stdout)

    def test_a_failed_warmup_call_fails_the_run_without_touching_the_medians(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            # Call 1 is the cold build; call 2 is the warmup build.
            proc = run_script(root, env_extra={"FAKE_FAIL_CALL": "2"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            self.assertEqual(res["verdict"]["verdict"], "measurement_failed")
            self.assertEqual(res["verdict"]["problems"],
                             ["warmup call 0: exit 3: fake failure"])
            self.assertEqual((res["warm"]["trials"], res["warm"]["failed_trials"]), (4, 0))
            self.assertEqual([s["ok"] for s in res["sequence"]], [False] + [True] * 4)

    def test_a_cold_seed_count_mismatch_stops_before_the_warm_calls(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_SEEDED": "5"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            self.assertEqual(res["verdict"]["verdict"], "measurement_failed")
            self.assertTrue(res["verdict"]["problems"][0].startswith("cold: shards_seeded 5"))
            self.assertNotIn("warm", res)
            self.assertEqual(len(read_calls(root)), 1)
            # A failed run still removes its scratch root, read-only store included.
            self.assertEqual(list((root / "scratch").iterdir()), [])


class InProcessTests(unittest.TestCase):
    def run_main(self, argv, env):
        err = io.StringIO()
        with mock.patch.dict(os.environ, env, clear=True), contextlib.redirect_stderr(err), \
                contextlib.redirect_stdout(io.StringIO()):
            code = mod.main(argv)
        return code, err.getvalue()

    def test_a_busy_node_needs_the_flag(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            stub, bin_dir = make_stub(root), make_fake_lean(root)
            scratch = root / "scratch"
            scratch.mkdir()
            with mock.patch("os.getloadavg", return_value=(50.0, 50.0, 50.0)):
                code, err = self.run_main(
                    ["--turbo-lean-bin", str(stub), "--scratch-dir", str(scratch)],
                    clean_env(PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", "")))
            self.assertEqual(code, 4)
            self.assertIn("load average", err)
            self.assertEqual(list(scratch.iterdir()), [])

    def test_missing_lean_is_an_environment_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            stub = make_stub(root)
            empty = root / "empty-bin"
            empty.mkdir()
            code, err = self.run_main(["--turbo-lean-bin", str(stub), "--allow-busy-node"],
                                      clean_env(PATH=str(empty)))
            self.assertEqual(code, 4)
            self.assertIn("lean is not on PATH", err)

    def test_an_unwritable_out_directory_is_an_environment_error_before_any_call(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            stub, bin_dir = make_stub(root), make_fake_lean(root)
            scratch = root / "scratch"
            scratch.mkdir()
            log = root / "calls.jsonl"
            code, err = self.run_main(
                ["--turbo-lean-bin", str(stub), "--allow-busy-node",
                 "--scratch-dir", str(scratch), "--out", str(root / "missing" / "out.json")],
                clean_env(PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""),
                          FAKE_LOG=str(log)))
            self.assertEqual(code, 4)
            self.assertIn("--out", err)
            self.assertFalse(log.exists(), "a call ran before the --out check")
            self.assertEqual(list(scratch.iterdir()), [])

    def test_a_binary_that_cannot_be_launched_is_an_environment_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            bin_dir = make_fake_lean(root)
            broken = root / "broken-turbo-lean"
            broken.write_text("#!/nonexistent/interpreter\n")
            broken.chmod(0o755)
            scratch = root / "scratch"
            scratch.mkdir()
            code, err = self.run_main(
                ["--turbo-lean-bin", str(broken), "--allow-busy-node",
                 "--scratch-dir", str(scratch), "--out", str(root / "out.json")],
                clean_env(PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", "")))
            self.assertEqual(code, 4, err)
            self.assertIn("launch", err)
            self.assertEqual(list(scratch.iterdir()), [])

    def test_an_existing_out_file_of_another_schema_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            stub, bin_dir = make_stub(root), make_fake_lean(root)
            scratch = root / "scratch"
            scratch.mkdir()
            env = clean_env(PATH=str(bin_dir) + os.pathsep + os.environ.get("PATH", ""))
            artifact = SCRIPT.parent / "bench_build_loop_g2b.json"
            cases = {"g2b-record.json": artifact.read_text(),
                     "other-kind.json": json.dumps({"schema_version": mod.SCHEMA_VERSION,
                                                    "kind": "check_loop_results"}),
                     "not-json.json": "plain text"}
            for name, text in cases.items():
                with self.subTest(name=name):
                    out = root / name
                    out.write_text(text)
                    code, err = self.run_main(
                        ["--turbo-lean-bin", str(stub), "--allow-busy-node",
                         "--scratch-dir", str(scratch), "--out", str(out)], env)
                    self.assertEqual(code, 4, err)
                    self.assertIn("--out", err)
                    self.assertEqual(out.read_text(), text)
            self.assertEqual(list(scratch.iterdir()), [])

    def test_a_previous_result_of_this_schema_may_be_replaced(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            out = root / "out.json"
            out.write_text(json.dumps({"schema_version": mod.SCHEMA_VERSION,
                                       "kind": "build_loop_results"}))
            mod.refuse_other_artifact(out)
            mod.refuse_other_artifact(root / "missing.json")

    def test_usage_errors_exit_2(self):
        for argv in (["--trials", "0"], ["--warmup", "-1"], ["--modules", "0"],
                     ["--theorems-per-module", "0"], ["--build-timeout-s", "0"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as cm:
                    mod.main(argv)
                self.assertEqual(cm.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
