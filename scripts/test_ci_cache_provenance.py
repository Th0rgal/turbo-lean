#!/usr/bin/env python3
"""CLI regression: cached outputs must not invent sandbox provenance.

Run with a turbo-lean binary and a working Lean toolchain in the environment.
Uses a private project/cache; never writes the machine's shared cache.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())
env = dict(os.environ, TURBO_LEAN_NO_DAEMON="1", TURBO_LEAN_NO_REMOTE_TELEMETRY="1")
with tempfile.TemporaryDirectory(prefix="turbo-ci-provenance-") as tmp:
    root = Path(tmp)
    project = root / "project"
    project.mkdir()
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
    (project / "lakefile.toml").write_text(
        'name = "demo"\ndefaultTargets = ["Demo"]\n[[lean_lib]]\nname = "Demo"\n'
    )
    (project / "Demo.lean").write_text("theorem sample (n : Nat) : n + 0 = n := by simp\n")
    command = [binary, "--cache-dir", str(root / "cache"), "--json", "ci-verify",
               "--project-dir", str(project), "--mode", "trusted"]
    first = json.loads(subprocess.check_output(command, env=env, text=True))
    cached = json.loads(subprocess.check_output(command, env=env, text=True))
    assert first["build_status"] == "built_and_verified", first
    assert first["bwrap_sandbox_used"] is False, first
    assert cached["build_status"].startswith("cache_hit"), cached
    assert cached["bwrap_sandbox_used"] is None, cached
    assert cached["bwrap_net_isolated"] is None, cached
    assert cached["receipt_blake3"] == first["receipt_blake3"]
    print("PASS: observed trusted build=false; cached provenance=unknown; receipt preserved")
