#!/usr/bin/env python3
"""Contract tests for `scripts/bench_build_loop.py` (G2b build-shaped warm loop).

Run: python3 scripts/test_bench_build_loop.py
No Lean toolchain or turbo-lean build required: the end-to-end cases drive the
script with a stub binary that emulates `build --json` (cold seeded build, then
warm cache hits that replay only when TURBO_LEAN_WARM_CAS_REPLAY=1 reaches it).
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parent / "bench_build_loop.py"
SWITCH_ON = "TURBO_LEAN_WARM_CAS_REPLAY"
SWITCH_OFF = "TURBO_LEAN_NO_WARM_CAS_REPLAY"


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
        sys.exit(3)
if seed:
    out = {"status": "built", "shards_seeded": int(os.environ.get("FAKE_SEEDED", theorems)),
           "cas_expr_replay_mode": "off", "cas_expr_replayed": 0,
           "cas_expr_replay_missing": 0, "cas_expr_replay_invalid": 0,
           "modules_total": 3, "modules_compiled": 3, "artifacts_stored": 7,
           "materialized_files": 7, "elapsed_ms": 40}
else:
    opted = (os.environ.get("TURBO_LEAN_WARM_CAS_REPLAY") == "1"
             and not os.environ.get("FAKE_BREAK_ON"))
    out = {"status": "cache_hit",
           "cas_expr_replay_mode": "warm_opt_in" if opted else "off",
           "cas_expr_replayed": theorems if opted else 0,
           "cas_expr_replay_missing": 0, "cas_expr_replay_invalid": 0,
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


def clean_env(**extra):
    env = {k: v for k, v in os.environ.items() if k not in (SWITCH_ON, SWITCH_OFF)}
    env.update(extra)
    return env


def run_script(root: Path, extra=(), env_extra=None, trials=4, warmup=1):
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
    return subprocess.run(cmd, capture_output=True, text=True, timeout=300, env=env)


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

    def test_classify_delta_is_the_check_loop_gate_with_off_as_baseline(self):
        self.assertAlmostEqual(
            mod.bcl.tolerance_ms(100.0, 0.0, "warm_cache_hit_daemon"), 135.0)
        self.assertEqual(mod.classify_delta(100.0, 0.0, 136.0)["class"], "regressed")
        self.assertEqual(mod.classify_delta(100.0, 0.0, 135.0)["class"], "unchanged")
        self.assertEqual(mod.classify_delta(100.0, 0.0, 65.0)["class"], "unchanged")
        self.assertEqual(mod.classify_delta(100.0, 0.0, 64.0)["class"], "improved")
        # OFF's own spread widens the band past the 10% floor (2 x 0.2 = 40%).
        wide = mod.classify_delta(100.0, 0.2, 150.0)
        self.assertEqual((wide["noise_band_ms"], wide["class"]), (65.0, "unchanged"))
        d = mod.classify_delta(100.0, 0.0, 110.0)
        self.assertEqual((d["delta_ms"], d["delta_pct"], d["noise_band_ms"]), (10.0, 10.0, 35.0))

    def test_rounds_alternate_abba(self):
        self.assertEqual([s for r in range(4) for s in mod.round_sides(r)],
                         ["on", "off", "off", "on", "on", "off", "off", "on"])

    def test_paired_differences_pair_measured_healthy_rounds(self):
        def t(rnd, side, wall, measured=True, problem=None):
            return {"round": rnd, "side": side, "external_wall_ms": wall,
                    "measured": measured, "problem": problem}
        trials = [t(0, "on", 999.0, measured=False), t(0, "off", 1.0, measured=False),
                  t(1, "off", 10.0), t(1, "on", 12.0),
                  t(2, "on", 9.0), t(2, "off", 10.0),
                  t(3, "off", 10.0, problem="exit 1"), t(3, "on", 50.0)]
        p = mod.paired_differences(trials, lambda x: x["external_wall_ms"])
        self.assertEqual((p["rounds"], p["median_ms"], p["on_slower_rounds"]), (2, 0.5, 1))


class ExpectationTests(unittest.TestCase):
    OK_ON = {"exit_code": 0, "json": {
        "status": "cache_hit", "cas_expr_replay_mode": "warm_opt_in",
        "cas_expr_replayed": 6, "cas_expr_replay_missing": 0,
        "cas_expr_replay_invalid": 0}}

    def with_json(self, **changes):
        return dict(self.OK_ON, json=dict(self.OK_ON["json"], **changes))

    def test_each_side_is_held_to_its_own_expectation(self):
        self.assertIsNone(mod.trial_problem(self.OK_ON, "on", 6))
        self.assertIn("expected ('off', 0)", mod.trial_problem(self.OK_ON, "off", 6))
        off = self.with_json(cas_expr_replay_mode="off", cas_expr_replayed=0)
        self.assertIsNone(mod.trial_problem(off, "off", 6))

    def test_an_opt_in_that_never_reaches_the_replay_is_a_failed_trial(self):
        not_reached = self.with_json(cas_expr_replay_mode="off", cas_expr_replayed=0)
        self.assertIn("expected ('warm_opt_in', 6)", mod.trial_problem(not_reached, "on", 6))
        short = self.with_json(cas_expr_replayed=5)
        self.assertIn("expected ('warm_opt_in', 6)", mod.trial_problem(short, "on", 6))

    def test_missing_invalid_status_exit_and_json_are_checked(self):
        self.assertIn("cas_expr_replay_invalid 1",
                      mod.trial_problem(self.with_json(cas_expr_replay_invalid=1), "on", 6))
        self.assertIn("cas_expr_replay_missing 2",
                      mod.trial_problem(self.with_json(cas_expr_replay_missing=2), "on", 6))
        self.assertIn("expected 'cache_hit'",
                      mod.trial_problem(self.with_json(status="built"), "on", 6))
        self.assertEqual(mod.trial_problem({"exit_code": 3, "json": None, "stderr": "boom\n"},
                                           "on", 6), "exit 3: boom")
        self.assertEqual(mod.trial_problem({"exit_code": 0, "json": None}, "off", 6),
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


class EndToEndTests(unittest.TestCase):
    def test_measures_both_sides_and_drives_the_switches_per_side(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            text = (root / "out.json").read_text()
            res = json.loads(text)
            self.assertEqual(res["verdict"], {"verdict": "measured", "problems": []})
            self.assertEqual((res["cold"]["status"], res["cold"]["shards_seeded"],
                              res["cold"]["problem"]), ("built", 6, None))
            self.assertEqual(res["fixture"]["theorems"], 6)
            on, off = res["sides"]["on"], res["sides"]["off"]
            self.assertEqual((on["trials"], on["failed_trials"]), (4, 0))
            self.assertEqual((off["trials"], off["failed_trials"]), (4, 0))
            self.assertEqual((on["replay"]["modes_observed"], on["replay"]["replayed_observed"]),
                             (["warm_opt_in"], [6]))
            self.assertEqual((off["replay"]["modes_observed"], off["replay"]["replayed_observed"]),
                             (["off"], [0]))
            for side in (on, off):
                self.assertIsNotNone(side["iqr_ms"])
                self.assertEqual(side["tool_elapsed_ms"]["n"], 4)
                self.assertNotIn("coverage_ratio_min", side)
            self.assertIn(res["delta"]["external_wall"]["class"],
                          ("unchanged", "regressed", "improved"))
            self.assertEqual(res["delta"]["paired_external_wall"]["rounds"], 4)
            self.assertEqual(res["delta"]["replayed_shards_per_on_call"], 6)
            seq = res["sequence"]
            self.assertEqual([s["side"] for s in seq],
                             ["on", "off", "off", "on", "on", "off", "off", "on", "on", "off"])
            self.assertEqual([s["measured"] for s in seq], [False, False] + [True] * 8)
            # What each call received: the cold build seeds with no switch; every
            # warm call omits --seed-shards; ON gets the opt-in, OFF gets nothing;
            # the opt-out never appears; no daemon and no telemetry anywhere.
            calls = read_calls(root)
            self.assertEqual(len(calls), 11)
            self.assertEqual((calls[0]["seed"], calls[0]["warm"], calls[0]["no_warm"]),
                             (True, None, None))
            for call, step in zip(calls[1:], seq):
                self.assertFalse(call["seed"])
                self.assertEqual(call["warm"], "1" if step["side"] == "on" else None)
            for call in calls:
                self.assertTrue(call["build"])
                self.assertIsNone(call["no_warm"])
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

    def test_an_opt_in_that_never_reaches_the_replay_fails_the_run(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_BREAK_ON": "1"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            v = res["verdict"]
            self.assertEqual(v["verdict"], "measurement_failed")
            self.assertTrue(v["problems"])
            self.assertTrue(all(p.startswith("on") for p in v["problems"]), v["problems"])
            self.assertIn("expected ('warm_opt_in', 6)", v["problems"][0])
            self.assertEqual(res["sides"]["on"]["failed_trials"], 4)
            self.assertEqual(res["sides"]["off"]["failed_trials"], 0)
            self.assertIn("VERDICT: measurement_failed", proc.stdout)

    def test_a_failed_warmup_call_fails_the_run_without_touching_the_medians(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            # Call 1 is the cold build; call 2 is round 0's first side, ON (warmup).
            proc = run_script(root, env_extra={"FAKE_FAIL_CALL": "2"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            self.assertEqual(res["verdict"]["verdict"], "measurement_failed")
            self.assertEqual(res["verdict"]["problems"],
                             ["on warmup round 0: exit 3: fake failure"])
            for side in ("on", "off"):
                self.assertEqual((res["sides"][side]["trials"],
                                  res["sides"][side]["failed_trials"]), (4, 0))
            self.assertEqual([s["ok"] for s in res["sequence"]], [False] + [True] * 9)

    def test_a_cold_seed_count_mismatch_stops_before_the_warm_rounds(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td).resolve()
            proc = run_script(root, env_extra={"FAKE_SEEDED": "5"})
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            res = json.loads((root / "out.json").read_text())
            self.assertEqual(res["verdict"]["verdict"], "measurement_failed")
            self.assertTrue(res["verdict"]["problems"][0].startswith("cold: shards_seeded 5"))
            self.assertNotIn("sides", res)
            self.assertEqual(len(read_calls(root)), 1)

    def test_an_ambient_replay_switch_is_refused_before_any_call(self):
        for var, val in ((SWITCH_OFF, "1"), (SWITCH_ON, "0")):
            with self.subTest(var=var), tempfile.TemporaryDirectory() as td:
                root = Path(td).resolve()
                proc = run_script(root, env_extra={var: val})
                self.assertEqual(proc.returncode, 4, proc.stdout + proc.stderr)
                self.assertIn(var, proc.stderr)
                self.assertEqual(read_calls(root), [])
                self.assertFalse((root / "out.json").exists())


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

    def test_usage_errors_exit_2(self):
        for argv in (["--trials", "0"], ["--warmup", "-1"], ["--modules", "0"],
                     ["--theorems-per-module", "0"], ["--build-timeout-s", "0"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as cm:
                    mod.main(argv)
                self.assertEqual(cm.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
