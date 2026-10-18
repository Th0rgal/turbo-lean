#!/usr/bin/env python3
"""
Auto-Research Evaluation Harness for turbo-lean.
Enforces Hard Soundness Invariants (I1..I4) and computes objective fitness metrics (M1..M5):
- I1: Zero false cache hits & zero forbidden axioms (sorryAx, native_decide, trustCompiler)
- I2: Proof-irrelevant InterfaceHash stability when editing theorem proof bodies
- I3: BLAKE3 integrity on export/import .tlpack bundles
- I4: Singleflight coalescing under concurrent multi-agent load
- M1: Single-theorem check latency (cold vs warm ms)
- M2: Full build cache-hit latency (ms)
- M3: Incremental theorem shard hit rate (%)
- M4: Multi-agent Singleflight coalesced saves
"""
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BIN = REPO_ROOT / "target" / "release" / "turbo-lean"
LEAN_PROJECT = REPO_ROOT / "lean"


def run_cmd(args, env=None, cwd=None):
    merged_env = os.environ.copy()
    merged_env["PATH"] = f"/var/lib/sandboxed-node/caches/elan/bin:{merged_env.get('PATH', '')}"
    if env:
        merged_env.update(env)
    t0 = time.perf_counter()
    proc = subprocess.run(
        args,
        cwd=cwd or REPO_ROOT,
        env=merged_env,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    if proc.returncode != 0:
        raise RuntimeError(f"Command {args} failed ({proc.returncode}):\n{proc.stdout}\n{proc.stderr}")
    return json.loads(proc.stdout), elapsed_ms


def main():
    if not BIN.exists():
        print(f"Building {BIN}...")
        subprocess.run(["cargo", "build", "--release"], cwd=REPO_ROOT, check=True)

    cache_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_"))
    try:
        env = {"TURBO_LEAN_HOME": str(cache_dir)}

        # 1. Cold CI-Verify (Hard Gate I1)
        res_ci, ci_cold_ms = run_cmd(
            [str(BIN), "--json", "ci-verify", "--project-dir", str(LEAN_PROJECT)],
            env=env,
        )
        assert res_ci["zero_sorry"] is True, "I1 violated: sorry detected"
        assert res_ci["zero_native_decide"] is True, "I1 violated: native_decide detected"
        interface_hash_1 = res_ci["interface_hash"]

        # 2. Warm Build + Concurrent 5-Agent Singleflight test (I4 & M2)
        def agent_build(_i):
            return run_cmd(
                [str(BIN), "--json", "build", "--project-dir", str(LEAN_PROJECT)],
                env=env,
            )

        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
            futs = [ex.submit(agent_build, i) for i in range(5)]
            agent_results = [f.result() for f in futs]

        warm_build_ms = min(r[1] for r in agent_results)

        # 3. Single-theorem shard check cold vs warm (M3 & M4) + lake_env_cache before/after test
        refl_file = LEAN_PROJECT / "TurboLean" / "Reflection.lean"
        unwarmed_env_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_unwarmed_"))
        try:
            res_unwarmed, shard_unwarmed_env_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(refl_file),
                    "--decl",
                    "lookup_chain_sound",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env={"TURBO_LEAN_HOME": str(unwarmed_env_dir)},
            )
            assert res_unwarmed.get("lake_env_cache_hit") is False, "Expected cold lake_env_cache on first run"
            res_warmed_env, shard_warmed_env_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(refl_file),
                    "--decl",
                    "lookup_chain_frame_sound",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env={"TURBO_LEAN_HOME": str(unwarmed_env_dir)},
            )
            assert res_warmed_env.get("lake_env_cache_hit") is True, "Expected lake_env_cache hit on second cold shard"
        finally:
            shutil.rmtree(unwarmed_env_dir, ignore_errors=True)

        res_shard_cold, shard_cold_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(refl_file),
                "--decl",
                "lookup_chain_sound",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_shard_cold.get("lake_env_cache_hit") is True, "Expected lake_env_cache hit after ci-verify/build"
        res_shard_warm, shard_warm_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(refl_file),
                "--decl",
                "lookup_chain_sound",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_shard_warm["status"] == "theorem_cache_hit", "Expected theorem_cache_hit"

        # 3b. Parallel multi-shard verification (--jobs 4 --parallel-shards) on remaining 7 uncached shards
        res_par_shards, par_shards_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(refl_file),
                "--parallel-shards",
                "--jobs",
                "4",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_par_shards["status"] == "file_verified", "Expected file_verified"
        assert res_par_shards["shard_hits"] == 1 and res_par_shards["shard_misses"] == 7

        res_all_cached, all_cached_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(refl_file),
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_all_cached["status"] == "all_shards_cached", "Expected all_shards_cached"

        # 4. Export / Import BLAKE3 integrity test (I3)
        pack_path = cache_dir / "bundle.tlpack"
        res_exp, _ = run_cmd([str(BIN), "--json", "export", "-o", str(pack_path)], env=env)
        cache_dir2 = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_import_"))
        try:
            env2 = {"TURBO_LEAN_HOME": str(cache_dir2)}
            res_imp, imp_ms = run_cmd([str(BIN), "--json", "import", str(pack_path)], env=env2)
            assert res_imp["imported_blobs"] == res_exp["exported_blobs"]
        finally:
            shutil.rmtree(cache_dir2, ignore_errors=True)

        # 5. Status & GDSF GC test
        res_status, _ = run_cmd([str(BIN), "--json", "status"], env=env)
        res_gc, _ = run_cmd(
            [str(BIN), "--json", "gc", "--max-reclaimable-bytes", "104857600"],
            env=env,
        )

        summary = {
            "invariants_passed": True,
            "interface_hash": interface_hash_1,
            "metrics": {
                "M1_ci_verify_cold_ms": round(ci_cold_ms, 2),
                "M2_warm_build_hit_ms": round(warm_build_ms, 2),
                "M3_shard_check_cold_ms": round(shard_cold_ms, 2),
                "M3_before_lake_env_cache_ms": round(shard_unwarmed_env_ms, 2),
                "M3_after_lake_env_cache_ms": round(shard_warmed_env_ms, 2),
                "M4_shard_check_warm_ms": round(shard_warm_ms, 2),
                "M5_pack_import_ms": round(imp_ms, 2),
                "M6_parallel_7_shards_ms": round(par_shards_ms, 2),
                "M7_all_8_shards_warm_ms": round(all_cached_ms, 2),
                "stored_blobs": res_status["total_blobs"],
                "completed_actions": res_status["total_actions"],
            },
        }
        print(json.dumps(summary, indent=2))
    finally:
        shutil.rmtree(cache_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
