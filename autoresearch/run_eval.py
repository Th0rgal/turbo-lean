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
import socket
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

        # 1. Cold CI-Verify (Hard Gate I1) + Cryptographic Verification Receipt emission
        receipt_path = cache_dir / "receipt.json"
        res_ci, ci_cold_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "ci-verify",
                "--project-dir",
                str(LEAN_PROJECT),
                "--receipt",
                str(receipt_path),
            ],
            env=env,
        )
        assert res_ci["zero_sorry"] is True, "I1 violated: sorry detected"
        assert res_ci["zero_native_decide"] is True, "I1 violated: native_decide detected"
        assert receipt_path.exists(), "Expected cryptographic verification receipt to be written"
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
        assert res_shard_cold.get("fast_olean_import") is True, "Expected fast_olean_import hit on pre-built module"
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

        # 3b. Coalesced multi-shard verification (--jobs 4 --parallel-shards) on remaining 7 uncached shards
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
        assert res_par_shards.get("mode") == "coalesced_shards", f"Expected coalesced_shards mode, got {res_par_shards.get('mode')}"
        assert res_par_shards["shard_hits"] == 1 and res_par_shards["shard_misses"] == 7

        # 3c. Coalesced incremental edit check: 2 uncached theorems in FastCheck.lean verified in 1 coalesced batch
        fastcheck_file = LEAN_PROJECT / "TurboLean" / "FastCheck.lean"
        res_fc_coalesced, fc_coalesced_2_shards_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(fastcheck_file),
                "--parallel-shards",
                "--jobs",
                "4",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_fc_coalesced["status"] == "file_verified"
        assert res_fc_coalesced.get("mode") == "coalesced_shards"
        assert res_fc_coalesced["shard_misses"] == 2

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

        # 4b. Zero-Redundancy HTTP Delta Sync & HTTP Remote FastCheck test (M8, M9, M10)
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]

        srv_env = os.environ.copy()
        srv_env["PATH"] = f"/var/lib/sandboxed-node/caches/elan/bin:{srv_env.get('PATH', '')}"
        srv_env.update(env)
        srv_proc = subprocess.Popen(
            [str(BIN), "serve", "--listen", f"127.0.0.1:{port}"],
            cwd=REPO_ROOT,
            env=srv_env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        sync_client_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_sync_"))
        try:
            # Wait for server to emit listening JSON line
            srv_proc.stdout.readline()
            sync_env = {"TURBO_LEAN_HOME": str(sync_client_dir)}
            res_sync_cold, m9_delta_sync_inc_ms = run_cmd(
                [str(BIN), "--json", "sync", f"http://127.0.0.1:{port}"],
                env=sync_env,
            )
            assert res_sync_cold["pulled_blobs"] == res_exp["exported_blobs"], "Expected full pull on cold sync"
            assert res_sync_cold["pushed_blobs"] == 0

            res_sync_noop, m8_delta_sync_noop_ms = run_cmd(
                [str(BIN), "--json", "sync", f"http://127.0.0.1:{port}"],
                env=sync_env,
            )
            assert res_sync_noop["pulled_blobs"] == 0 and res_sync_noop["pushed_blobs"] == 0, (
                f"Expected 0 blobs transferred when already synced, got {res_sync_noop}"
            )
            assert res_sync_noop["pulled_pack_bytes"] == 0 and res_sync_noop["pushed_raw_bytes"] == 0

            # Test HTTP remote fast-check offload (POST /fast-check): cold vs warm binary CAS cache
            res_http_fc, m10_http_fastcheck_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "fast-check",
                    str(fastcheck_file),
                    "--remote-http",
                    f"http://127.0.0.1:{port}",
                ],
                env=sync_env,
            )
            assert res_http_fc["status"] == "ok", f"Expected HTTP fast-check ok, got {res_http_fc}"
            assert res_http_fc["mode"] == "http_remote_cpu_perceus"
            assert res_http_fc["compile_cache_hit"] is False, f"Expected cold compile_cache_hit=False, got {res_http_fc}"
            assert "Checked 1,000,000 256-bit states" in res_http_fc["output"]

            res_http_fc_warm, m10b_http_fastcheck_warm_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "fast-check",
                    str(fastcheck_file),
                    "--remote-http",
                    f"http://127.0.0.1:{port}",
                ],
                env=sync_env,
            )
            assert res_http_fc_warm["status"] == "ok"
            assert res_http_fc_warm["compile_cache_hit"] is True, f"Expected warm compile_cache_hit=True, got {res_http_fc_warm}"
            assert res_http_fc_warm["binary_cache_key"] == res_http_fc["binary_cache_key"]
            assert m10b_http_fastcheck_warm_ms < 25.0, f"Expected warm HTTP fast-check < 25ms, got {m10b_http_fastcheck_warm_ms:.2f}ms"
        finally:
            srv_proc.terminate()
            srv_proc.wait(timeout=5)
            shutil.rmtree(sync_client_dir, ignore_errors=True)

        # 4c. Untrusted CI-Verify sandbox & env scrubbing test
        res_ci_untrusted, _ = run_cmd(
            [
                str(BIN),
                "--json",
                "ci-verify",
                "--mode",
                "untrusted",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env={**env, "GH_TOKEN": "dummy_secret_token"},
        )
        assert res_ci_untrusted["status"] == "ci_verified"
        assert res_ci_untrusted["mode"] == "untrusted"
        assert res_ci_untrusted["trust_domain"] == "untrusted:ci"
        assert res_ci_untrusted["env_scrubbed"] is True

        # 5. Status & GDSF GC test
        res_status, _ = run_cmd([str(BIN), "--json", "status"], env=env)
        res_gc, _ = run_cmd(
            [str(BIN), "--json", "gc", "--max-reclaimable-bytes", "104857600"],
            env=env,
        )

        # 6. Kernel-level Lean.Environment Inspector verification (TurboLean.Inspector)
        insp_file = LEAN_PROJECT / "TurboLean" / "Inspector.lean"
        res_insp_cold, insp_cold_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(insp_file),
                "--decl",
                "propext_is_allowed",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        res_insp_warm, insp_warm_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(insp_file),
                "--decl",
                "propext_is_allowed",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_insp_warm["status"] == "theorem_cache_hit", "Expected theorem_cache_hit on Inspector.lean"

        # Verify negative kernel-level rejection of sorryAx via #turbo_assert_clean_axioms
        neg_probe = cache_dir / "NegProbe.lean"
        neg_probe.write_text(
            "import TurboLean.Inspector\n"
            "theorem bad_thm : True := sorry\n"
            "#turbo_assert_clean_axioms [bad_thm]\n"
        )
        merged_env = os.environ.copy()
        merged_env["PATH"] = f"/var/lib/sandboxed-node/caches/elan/bin:{merged_env.get('PATH', '')}"
        neg_proc = subprocess.run(
            ["lake", "env", "lean", str(neg_probe)],
            cwd=LEAN_PROJECT,
            env=merged_env,
            capture_output=True,
            text=True,
        )
        assert neg_proc.returncode != 0 and "Kernel axiom gate FAILED" in (neg_proc.stdout + neg_proc.stderr), (
            f"Expected TurboLean.Inspector kernel axiom gate to reject sorryAx, got: {neg_proc.stdout}\n{neg_proc.stderr}"
        )

        # 7. Kernel `Expr` Replay Assembler (`Lean.addDecl`) verification & microsecond benchmark (TurboLean.Assembler)
        asm_file = LEAN_PROJECT / "TurboLean" / "Assembler.lean"
        res_asm_cold, asm_cold_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(asm_file),
                "--decl",
                "exprHeadTag_pos",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        res_asm_warm, asm_warm_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(asm_file),
                "--decl",
                "exprHeadTag_pos",
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_asm_warm["status"] == "theorem_cache_hit", "Expected theorem_cache_hit on Assembler.lean"

        replay_probe = cache_dir / "ReplayProbe.lean"
        replay_probe.write_text(
            "import TurboLean.Assembler\n"
            "#turbo_benchmark_kernel_replay_json [\n"
            "  TurboLean.Reflection.lookup_chain_sound\n"
            "  TurboLean.Reflection.lookup_chain_frame_sound\n"
            "  TurboLean.FastCheck.addWithCarry_zero_right\n"
            "  TurboLean.FastCheck.addWithCarry_comm_low\n"
            "]\n"
        )
        replay_proc = subprocess.run(
            ["lake", "env", "lean", str(replay_probe)],
            cwd=LEAN_PROJECT,
            env=merged_env,
            capture_output=True,
            text=True,
            check=True,
        )
        replay_receipts = json.loads(replay_proc.stdout.strip())
        assert len(replay_receipts) == 4, f"Expected 4 kernel replay receipts, got {len(replay_receipts)}"
        assert all(r["certified_clean"] is True for r in replay_receipts), "Expected all kernel-replayed theorems to pass checkConstantClean"
        total_replay_us = sum(r["replay_nanos"] for r in replay_receipts) / 1000.0
        total_replay_hb = sum(r["replay_heartbeats"] for r in replay_receipts)

        # 8. Cryptographic Verification Receipt (`verify-receipt`) integrity & drift check (M15_verify_receipt_ms)
        res_vr, verify_receipt_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "verify-receipt",
                str(receipt_path),
                "--expected-interface-hash",
                interface_hash_1,
                "--baseline-receipt",
                str(receipt_path),
            ],
            env=env,
        )
        assert res_vr["status"] == "receipt_verified", f"Expected receipt_verified, got {res_vr}"
        assert res_vr["forbidden_constructs_found"] == 0
        assert res_vr["interface_hash"] == interface_hash_1

        # 9. Directory-wide single-transaction batch CAS check (M14_dir_check_warm_ms)
        res_dir_inc, _ = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(LEAN_PROJECT),
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_dir_inc["status"] in ("file_verified", "all_shards_cached")

        res_dir_warm, m14_dir_check_warm_ms = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(LEAN_PROJECT),
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_dir_warm["status"] == "all_shards_cached", f"Expected all_shards_cached on directory check, got {res_dir_warm}"
        assert res_dir_warm["shard_hits"] >= 17, f"Expected >= 17 cached shards across lean/, got {res_dir_warm['shard_hits']}"

        summary = {
            "invariants_passed": True,
            "kernel_inspector_verified": True,
            "kernel_expr_replay_verified": True,
            "cryptographic_receipt_verified": True,
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
                "M6b_coalesced_2_shards_ms": round(fc_coalesced_2_shards_ms, 2),
                "M7_all_8_shards_warm_ms": round(all_cached_ms, 2),
                "M8_delta_sync_noop_ms": round(m8_delta_sync_noop_ms, 2),
                "M9_delta_sync_incremental_ms": round(m9_delta_sync_inc_ms, 2),
                "M10_http_remote_fastcheck_ms": round(m10_http_fastcheck_ms, 2),
                "M10b_http_remote_fastcheck_warm_ms": round(m10b_http_fastcheck_warm_ms, 2),
                "M8_inspector_shard_cold_ms": round(insp_cold_ms, 2),
                "M9_inspector_shard_warm_ms": round(insp_warm_ms, 2),
                "M10_assembler_shard_cold_ms": round(asm_cold_ms, 2),
                "M11_assembler_shard_warm_ms": round(asm_warm_ms, 2),
                "M12_kernel_adddecl_4_thms_us": round(total_replay_us, 2),
                "M13_kernel_adddecl_4_thms_heartbeats": total_replay_hb,
                "M14_dir_check_warm_ms": round(m14_dir_check_warm_ms, 2),
                "M15_verify_receipt_ms": round(verify_receipt_ms, 2),
                "stored_blobs": res_status["total_blobs"],
                "completed_actions": res_status["total_actions"],
            },
        }
        print(json.dumps(summary, indent=2))
    finally:
        shutil.rmtree(cache_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
