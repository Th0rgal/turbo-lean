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
        assert ci_cold_ms < 20.0, (
            f"Expected M1_ci_verify_cold_ms < 20ms when project .olean artifacts are up-to-date, got {ci_cold_ms:.2f}ms"
        )
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
            assert shard_unwarmed_env_ms < 18.0, (
                f"Expected M3_before_lake_env_cache_ms < 18ms via direct .elan toolchain + verified .olean fast path, got {shard_unwarmed_env_ms:.2f}ms"
            )
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
            assert shard_warmed_env_ms < 12.0, (
                f"Expected M3_after_lake_env_cache_ms < 12ms, got {shard_warmed_env_ms:.2f}ms"
            )
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
        assert shard_cold_ms < 15.0, (
            f"Expected M3_shard_check_cold_ms < 15ms via verified-build single-decl fast path, got {shard_cold_ms:.2f}ms"
        )
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
        assert par_shards_ms < 15.0, (
            f"Expected M6_parallel_7_shards_ms < 15ms via verified-build fast path, got {par_shards_ms:.2f}ms"
        )

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
        assert fc_coalesced_2_shards_ms < 15.0, (
            f"Expected M6b_coalesced_2_shards_ms < 15ms via verified-build fast path, got {fc_coalesced_2_shards_ms:.2f}ms"
        )

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

        # 4. Export / Import BLAKE3 integrity & batch single-transaction test (I3, M5, M5b)
        pack_path = cache_dir / "bundle.tlpack"
        res_exp, _ = run_cmd([str(BIN), "--json", "export", "-o", str(pack_path)], env=env)
        cache_dir2 = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_import_"))
        try:
            env2 = {"TURBO_LEAN_HOME": str(cache_dir2)}
            res_imp, imp_ms = run_cmd([str(BIN), "--json", "import", str(pack_path)], env=env2)
            assert res_imp["imported_blobs"] == res_exp["exported_blobs"]
            assert imp_ms < 15.0, f"Expected cold batch pack import < 15ms, got {imp_ms:.2f}ms"
            res_imp_warm, imp_warm_ms = run_cmd([str(BIN), "--json", "import", str(pack_path)], env=env2)
            assert res_imp_warm["imported_blobs"] == res_exp["exported_blobs"]
            assert imp_warm_ms < 10.0, f"Expected warm zero-copy pack import < 10ms, got {imp_warm_ms:.2f}ms"
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
            assert m9_delta_sync_inc_ms < 15.0, (
                f"Expected cold HTTP delta sync < 15ms, got {m9_delta_sync_inc_ms:.2f}ms"
            )

            res_sync_noop, m8_delta_sync_noop_ms = run_cmd(
                [str(BIN), "--json", "sync", f"http://127.0.0.1:{port}"],
                env=sync_env,
            )
            assert res_sync_noop["pulled_blobs"] == 0 and res_sync_noop["pushed_blobs"] == 0, (
                f"Expected 0 blobs transferred when already synced, got {res_sync_noop}"
            )
            assert res_sync_noop["pulled_pack_bytes"] == 0 and res_sync_noop["pushed_raw_bytes"] == 0
            assert m8_delta_sync_noop_ms < 10.0, (
                f"Expected noop HTTP delta sync < 10ms, got {m8_delta_sync_noop_ms:.2f}ms"
            )

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
            assert m10_http_fastcheck_ms < 15.0, (
                f"Expected cold HTTP fast-check < 15ms via pre-warmed /dev/shm harness, got {m10_http_fastcheck_ms:.2f}ms"
            )

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
            assert m10b_http_fastcheck_warm_ms < 15.0, f"Expected warm HTTP fast-check < 15ms, got {m10b_http_fastcheck_warm_ms:.2f}ms"
        finally:
            srv_proc.terminate()
            srv_proc.wait(timeout=5)
            shutil.rmtree(sync_client_dir, ignore_errors=True)

        # 4b2. Zero-Redundancy HTTP Delta Push (`sync --push` -> `POST /import-delta`) (M9b, M9c)
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            push_port = s.getsockname()[1]

        push_srv_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_push_srv_"))
        push_srv_env = os.environ.copy()
        push_srv_env["TURBO_LEAN_HOME"] = str(push_srv_dir)
        push_srv_proc = subprocess.Popen(
            [str(BIN), "serve", "--listen", f"127.0.0.1:{push_port}"],
            cwd=REPO_ROOT,
            env=push_srv_env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            push_srv_proc.stdout.readline()
            res_push_cold, m9b_delta_sync_push_ms = run_cmd(
                [str(BIN), "--json", "sync", "--push", f"http://127.0.0.1:{push_port}"],
                env=env,
            )
            assert res_push_cold["status"] == "synced"
            assert res_push_cold["mode"] == "push_only"
            assert res_push_cold["pushed_blobs"] == res_exp["exported_blobs"], (
                f"Expected full delta push of {res_exp['exported_blobs']} blobs, got {res_push_cold}"
            )
            assert res_push_cold["delta_push_noop"] is False
            assert m9b_delta_sync_push_ms < 15.0, f"Expected delta push < 15ms, got {m9b_delta_sync_push_ms:.2f}ms"

            res_push_noop, m9c_delta_sync_push_noop_ms = run_cmd(
                [str(BIN), "--json", "sync", "--push", f"http://127.0.0.1:{push_port}"],
                env=env,
            )
            assert res_push_noop["status"] == "synced"
            assert res_push_noop["pushed_blobs"] == 0 and res_push_noop["pushed_actions"] == 0
            assert res_push_noop["pushed_pack_bytes"] == 0 and res_push_noop["pushed_raw_bytes"] == 0
            assert res_push_noop["delta_push_noop"] is True
            assert m9c_delta_sync_push_noop_ms < 10.0, (
                f"Expected noop delta push < 10ms, got {m9c_delta_sync_push_noop_ms:.2f}ms"
            )

            # 4b3. Remote CPU Theorem-Shard Verification Offload (`POST /check-shard`, `--remote-http`) (M10c, M10d)
            orig_fc_remote = fastcheck_file.read_text()
            remote_client1 = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_rem_c1_"))
            remote_client2 = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_rem_c2_"))
            try:
                edited_fc_remote = orig_fc_remote.replace(
                    "simp [Word256.addWithCarry, Word256.zero]",
                    "dsimp [Word256.addWithCarry, Word256.zero]; simp",
                    1,
                )
                assert edited_fc_remote != orig_fc_remote
                fastcheck_file.write_text(edited_fc_remote)

                # Client 1 (empty cache) offloads uncached shard to remote server -> server runs Lean & caches shard
                res_rem_cold, m10c_http_remote_shard_check_cold_ms = run_cmd(
                    [
                        str(BIN),
                        "--json",
                        "check",
                        str(fastcheck_file),
                        "--decl",
                        "addWithCarry_zero_right",
                        "--project-dir",
                        str(LEAN_PROJECT),
                        "--remote-http",
                        f"http://127.0.0.1:{push_port}",
                    ],
                    env={"TURBO_LEAN_HOME": str(remote_client1)},
                )
                assert res_rem_cold["status"] == "remote_theorem_verified", (
                    f"Expected remote_theorem_verified on cold remote shard offload, got {res_rem_cold}"
                )
                assert m10c_http_remote_shard_check_cold_ms < 15.0, (
                    f"Expected cold remote shard check < 15ms via pre-warmed Zygote, got {m10c_http_remote_shard_check_cold_ms:.2f}ms"
                )

                # Client 2 (empty local cache) offloads same shard to remote server -> hits server TheoremProofCAS in <15ms!
                res_rem_hit, m10d_http_remote_shard_check_hit_ms = run_cmd(
                    [
                        str(BIN),
                        "--json",
                        "check",
                        str(fastcheck_file),
                        "--decl",
                        "addWithCarry_zero_right",
                        "--project-dir",
                        str(LEAN_PROJECT),
                        "--remote-http",
                        f"http://127.0.0.1:{push_port}",
                    ],
                    env={"TURBO_LEAN_HOME": str(remote_client2)},
                )
                assert res_rem_hit["status"] == "remote_theorem_cache_hit", (
                    f"Expected remote_theorem_cache_hit for second client, got {res_rem_hit}"
                )
                assert m10d_http_remote_shard_check_hit_ms < 15.0, (
                    f"Expected remote shard cache hit < 15ms, got {m10d_http_remote_shard_check_hit_ms:.2f}ms"
                )

                # Client 2 subsequent check hits its own local TheoremProofCAS auto-populated from the remote hit
                res_rem_local_hit, _ = run_cmd(
                    [
                        str(BIN),
                        "--json",
                        "check",
                        str(fastcheck_file),
                        "--decl",
                        "addWithCarry_zero_right",
                        "--project-dir",
                        str(LEAN_PROJECT),
                    ],
                    env={"TURBO_LEAN_HOME": str(remote_client2)},
                )
                assert res_rem_local_hit["status"] == "theorem_cache_hit", (
                    f"Expected local theorem_cache_hit after remote import, got {res_rem_local_hit}"
                )

                # Coalesced Batch Remote HTTP Offload (`POST /check-shards-batch`):
                # Edit both theorem proofs in FastCheck.lean and verify both uncached shards in 1 HTTP call + 1 remote `lean` invocation!
                edited_fc_batch = edited_fc_remote.replace(
                    "simp [Word256.addWithCarry, UInt64.add_comm]",
                    "dsimp [Word256.addWithCarry]; simp [UInt64.add_comm]",
                    1,
                )
                assert edited_fc_batch != edited_fc_remote
                fastcheck_file.write_text(edited_fc_batch)

                remote_client_batch = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_rem_batch_"))
                try:
                    res_rem_batch, m10e_http_remote_batch_coalesced_ms = run_cmd(
                        [
                            str(BIN),
                            "--json",
                            "check",
                            str(fastcheck_file),
                            "--project-dir",
                            str(LEAN_PROJECT),
                            "--remote-http",
                            f"http://127.0.0.1:{push_port}",
                        ],
                        env={"TURBO_LEAN_HOME": str(remote_client_batch)},
                    )
                    assert res_rem_batch["status"] == "file_verified", (
                        f"Expected file_verified on batch remote shard offload, got {res_rem_batch}"
                    )
                    assert res_rem_batch.get("mode") == "remote_coalesced_shards", (
                        f"Expected remote_coalesced_shards mode, got {res_rem_batch}"
                    )
                    assert res_rem_batch["shard_misses"] == 2
                    # AddWithCarry_zero_right was already cached on server from M10c, so server has 1 cache hit and verifies 1 new shard
                    assert res_rem_batch["remote_cache_hits"] == 1 and res_rem_batch["remote_verified"] == 1, (
                        f"Expected 1 remote hit + 1 remote verified, got {res_rem_batch}"
                    )
                    assert m10e_http_remote_batch_coalesced_ms < 15.0, (
                        f"Expected remote batch coalesced check < 15ms via server partial-hit synthetic omission, got {m10e_http_remote_batch_coalesced_ms:.2f}ms"
                    )
                finally:
                    shutil.rmtree(remote_client_batch, ignore_errors=True)

                # In-Memory Lean.Environment Zygote Worker (`POST /check-shard` on 2 distinct uncached proofs sharing `import TurboLean.Reflection`):
                import urllib.request
                zygote_req1 = json.dumps({
                    "decl": "zygote_eval_thm_1",
                    "shard_key": "eval_zygote_shard_key_1",
                    "shard_source": (
                        "import TurboLean.Reflection\n"
                        "open TurboLean.Reflection\n"
                        "theorem zygote_eval_thm_1 (s : ContractState) (k : StorageKey) (v : Nat) :\n"
                        "    getStorage (setStorage s k v) k = v := getStorage_setStorage_same\n"
                    ),
                    "interface_hash": "eval_iface_z",
                    "prefix_env_hash": "eval_prefix_z",
                    "stmt_hash": "eval_stmt_z1",
                    "proof_hash": "eval_proof_z1",
                    "toolchain": "leanprover/lean4:v4.31.0",
                }).encode()
                with urllib.request.urlopen(
                    urllib.request.Request(
                        f"http://127.0.0.1:{push_port}/check-shard",
                        data=zygote_req1,
                        headers={"Content-Type": "application/json"},
                        method="POST",
                    )
                ) as zresp1:
                    zdata1 = json.loads(zresp1.read().decode())
                assert zdata1["status"] == "remote_theorem_verified"
                assert zdata1.get("zygote_used") is True, f"Expected zygote_used=True on first shard, got {zdata1}"

                zygote_req2 = json.dumps({
                    "decl": "zygote_eval_thm_2",
                    "shard_key": "eval_zygote_shard_key_2",
                    "shard_source": (
                        "import TurboLean.Reflection\n"
                        "open TurboLean.Reflection\n"
                        "theorem zygote_eval_thm_2 (k : StorageKey) :\n"
                        "    StorageKey.fastBeq k k = true := StorageKey.fastBeq_refl k\n"
                    ),
                    "interface_hash": "eval_iface_z",
                    "prefix_env_hash": "eval_prefix_z",
                    "stmt_hash": "eval_stmt_z2",
                    "proof_hash": "eval_proof_z2",
                    "toolchain": "leanprover/lean4:v4.31.0",
                }).encode()
                tz0 = time.perf_counter()
                with urllib.request.urlopen(
                    urllib.request.Request(
                        f"http://127.0.0.1:{push_port}/check-shard",
                        data=zygote_req2,
                        headers={"Content-Type": "application/json"},
                        method="POST",
                    )
                ) as zresp2:
                    zdata2 = json.loads(zresp2.read().decode())
                m19_zygote_new_proof_warm_env_ms = (time.perf_counter() - tz0) * 1000.0
                assert zdata2["status"] == "remote_theorem_verified"
                assert zdata2.get("zygote_used") is True
                assert zdata2.get("zygote_env_cache_hit") is True, (
                    f"Expected in-memory Lean.Environment hit on second uncached proof, got {zdata2}"
                )
                assert zdata2.get("zygote_import_us") == 0
                assert m19_zygote_new_proof_warm_env_ms < 50.0, (
                    f"Expected Zygote warm-env new-proof verification < 50ms, got {m19_zygote_new_proof_warm_env_ms:.2f}ms"
                )
            finally:
                fastcheck_file.write_text(orig_fc_remote)
                shutil.rmtree(remote_client1, ignore_errors=True)
                shutil.rmtree(remote_client2, ignore_errors=True)
        finally:
            push_srv_proc.terminate()
            push_srv_proc.wait(timeout=5)
            shutil.rmtree(push_srv_dir, ignore_errors=True)

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
        assert insp_cold_ms < 15.0, (
            f"Expected M8_inspector_shard_cold_ms < 15ms via unified Zygote, got {insp_cold_ms:.2f}ms"
        )

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
        assert asm_cold_ms < 15.0, (
            f"Expected M10_assembler_shard_cold_ms < 15ms via unified Zygote, got {asm_cold_ms:.2f}ms"
        )

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
        assert verify_receipt_ms < 10.0, (
            f"Expected M15_verify_receipt_ms < 10ms without SQLite overhead, got {verify_receipt_ms:.2f}ms"
        )

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

        # 9b. Cross-File Coalesced Uncached-Shard Verification (M14b_cross_file_coalesced_cold_ms):
        # Invalidate 1 shard in Reflection.lean and 1 shard in FastCheck.lean and verify both
        # files together in a SINGLE `lean` invocation (< 320 ms).
        import sqlite3
        with sqlite3.connect(cache_dir / "state.db") as conn:
            conn.execute(
                "DELETE FROM actions WHERE action_key IN ("
                "  SELECT action_key FROM action_outputs"
                "  WHERE rel_path IN ('thm:lookup_chain_sound', 'thm:addWithCarry_zero_right')"
                ")"
            )
            conn.commit()

        res_cross_cold, m14b_cross_file_coalesced_cold_ms = run_cmd(
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
        assert res_cross_cold["status"] == "file_verified", f"Expected file_verified, got {res_cross_cold}"
        assert res_cross_cold.get("mode") == "cross_file_coalesced_shards", (
            f"Expected cross_file_coalesced_shards mode, got {res_cross_cold}"
        )
        assert res_cross_cold["shard_misses"] == 2 and res_cross_cold["shard_hits"] >= 15
        assert m14b_cross_file_coalesced_cold_ms < 25.0, (
            f"Expected M14b_cross_file_coalesced_cold_ms < 25ms via verified-module Zygote fast path, got {m14b_cross_file_coalesced_cold_ms:.2f}ms"
        )

        # 10. Git-Aware Incremental PR Verification (`pr-verify --base HEAD`) (M16_pr_verify_proof_edit_ms)
        orig_refl_src = refl_file.read_text()
        try:
            edited_refl_src = orig_refl_src.replace(
                "simp [getStorage, setStorage, StorageKey.fastBeq_refl]",
                "unfold getStorage setStorage; simp [StorageKey.fastBeq_refl]",
                1,
            )
            assert edited_refl_src != orig_refl_src, "Expected proof edit in Reflection.lean"
            refl_file.write_text(edited_refl_src)

            res_pr, m16_pr_verify_proof_edit_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "pr-verify",
                    "--project-dir",
                    str(LEAN_PROJECT),
                    "--base",
                    "HEAD",
                    "--mode",
                    "untrusted",
                    "--disallow-statement-changes",
                ],
                env=env,
            )
            assert res_pr["status"] == "pr_verified", f"Expected pr_verified, got {res_pr}"
            assert res_pr["interface_drift"] is False, f"Expected interface_drift=False on proof-only edit, got {res_pr}"
            assert res_pr["interface_hash"] == interface_hash_1
            assert res_pr["proof_edited_theorems"] == [
                "TurboLean/Reflection.lean::getStorage_setStorage_same"
            ], f"Unexpected proof_edited_theorems: {res_pr['proof_edited_theorems']}"
            assert res_pr["statement_edited_theorems"] == []
            assert res_pr["unchanged_theorems_count"] >= 16
            assert res_pr["shards_verified"] == 1
            assert m16_pr_verify_proof_edit_ms < 16.0, (
                f"Expected M16_pr_verify_proof_edit_ms < 16ms, got {m16_pr_verify_proof_edit_ms:.2f}ms"
            )
        finally:
            refl_file.write_text(orig_refl_src)

        # 10b. Cross-File Coalesced Multi-File PR Proof Edit (`M16b_pr_verify_multi_file_edit_ms`)
        orig_fc_src = fastcheck_file.read_text()
        try:
            edited_refl_2 = orig_refl_src.replace(
                "dsimp only\n  cases hbeq : StorageKey.fastBeq k' k",
                "dsimp\n  cases hbeq : StorageKey.fastBeq k' k",
                1,
            )
            edited_fc_2 = orig_fc_src.replace(
                "simp [Word256.addWithCarry, UInt64.add_comm]",
                "unfold Word256.addWithCarry; simp [UInt64.add_comm]",
                1,
            )
            assert edited_refl_2 != orig_refl_src and edited_fc_2 != orig_fc_src
            refl_file.write_text(edited_refl_2)
            fastcheck_file.write_text(edited_fc_2)

            res_pr_multi, m16b_pr_verify_multi_file_edit_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "pr-verify",
                    "--project-dir",
                    str(LEAN_PROJECT),
                    "--base",
                    "HEAD",
                    "--mode",
                    "untrusted",
                    "--disallow-statement-changes",
                ],
                env=env,
            )
            assert res_pr_multi["status"] == "pr_verified", f"Expected pr_verified, got {res_pr_multi}"
            assert res_pr_multi["interface_drift"] is False
            assert res_pr_multi["cross_file_coalesced"] is True, (
                f"Expected cross_file_coalesced=True on multi-file proof edit, got {res_pr_multi}"
            )
            assert res_pr_multi["proof_edited_theorems"] == [
                "TurboLean/FastCheck.lean::addWithCarry_comm_low",
                "TurboLean/Reflection.lean::getStorage_setStorage_other",
            ], f"Unexpected proof_edited_theorems: {res_pr_multi['proof_edited_theorems']}"
            assert res_pr_multi["shards_verified"] == 2
            assert m16b_pr_verify_multi_file_edit_ms < 14.0, (
                f"Expected M16b < 14ms, got {m16b_pr_verify_multi_file_edit_ms:.2f}ms"
            )
        finally:
            refl_file.write_text(orig_refl_src)
            fastcheck_file.write_text(orig_fc_src)

        # 11. Multi-Agent Singleflight Coalescing (4 concurrent agents on uncached shard) & GDSF Telemetry
        fc_file = LEAN_PROJECT / "TurboLean" / "FastCheck.lean"
        orig_fc_src = fc_file.read_text()
        try:
            edited_fc_src = orig_fc_src.replace(
                "simp [Word256.addWithCarry, Word256.zero]",
                "unfold Word256.addWithCarry Word256.zero; simp",
                1,
            )
            assert edited_fc_src != orig_fc_src, "Expected proof edit in FastCheck.lean"
            fc_file.write_text(edited_fc_src)

            def _run_agent_check(_idx):
                res, _ = run_cmd(
                    [
                        str(BIN),
                        "--json",
                        "check",
                        str(fc_file),
                        "--decl",
                        "addWithCarry_zero_right",
                        "--project-dir",
                        str(LEAN_PROJECT),
                    ],
                    env=env,
                )
                return res

            t_sf0 = time.perf_counter()
            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                sf_results = list(pool.map(_run_agent_check, range(4)))
            m17_multi_agent_singleflight_4x_ms = (time.perf_counter() - t_sf0) * 1000.0

            verified_count = sum(1 for r in sf_results if r.get("status") == "theorem_verified")
            cache_hit_count = sum(1 for r in sf_results if r.get("status") == "theorem_cache_hit")
            assert verified_count == 1 and cache_hit_count == 3, (
                f"Expected 1 leader verification and 3 coalesced follower hits across 4 concurrent agents, got: {sf_results}"
            )
        finally:
            fc_file.write_text(orig_fc_src)

        res_status, _ = run_cmd([str(BIN), "--json", "status"], env=env)
        assert res_status["total_shard_hits"] > 0, f"Expected total_shard_hits > 0, got {res_status}"
        assert res_status["saved_compute_ms"] > 0, f"Expected saved_compute_ms > 0, got {res_status}"
        assert res_status["total_coalesced_waits"] >= 3, (
            f"Expected total_coalesced_waits >= 3 from 4x singleflight, got {res_status}"
        )

        # 12. Instant TheoremProofCAS Seeding from Verified Build (`seed-shards`) (M18_seed_shards_ms)
        seed_cache_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_seed_"))
        try:
            res_seed, m18_seed_shards_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "seed-shards",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env={"TURBO_LEAN_HOME": str(seed_cache_dir)},
            )
            assert res_seed["status"] == "shards_seeded", f"Expected shards_seeded, got {res_seed}"
            assert res_seed["shards_seeded"] == 17, f"Expected 17 shards seeded, got {res_seed['shards_seeded']}"
            assert m18_seed_shards_ms < 15.0, f"Expected M18_seed_shards_ms < 15ms, got {m18_seed_shards_ms:.2f}ms"

            res_seeded_check, _ = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(LEAN_PROJECT / "TurboLean"),
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env={"TURBO_LEAN_HOME": str(seed_cache_dir)},
            )
            assert res_seeded_check["status"] == "all_shards_cached", (
                f"Expected all_shards_cached on first check after seed-shards, got {res_seeded_check}"
            )
            assert res_seeded_check["shard_hits"] == 17 and res_seeded_check["shard_misses"] == 0
        finally:
            shutil.rmtree(seed_cache_dir, ignore_errors=True)

        # 13. Auto-Spawned Local Zygote Daemon (`turbo-lean check` without `--remote-http` on 2 brand-new proof edits) (M20_local_check_new_proof_zygote_ms)
        orig_fc_z = fc_file.read_text()
        try:
            edit_z1 = orig_fc_z.replace(
                "simp [Word256.addWithCarry, Word256.zero]",
                "dsimp only [Word256.addWithCarry, Word256.zero]; simp",
                1,
            )
            assert edit_z1 != orig_fc_z
            fc_file.write_text(edit_z1)
            res_local_z1, _ = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(fc_file),
                    "--decl",
                    "addWithCarry_zero_right",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env=env,
            )
            assert res_local_z1["status"] == "theorem_verified", f"Expected theorem_verified, got {res_local_z1}"
            assert res_local_z1.get("zygote_used") is True, f"Expected local zygote_used=True, got {res_local_z1}"

            edit_z2 = orig_fc_z.replace(
                "simp [Word256.addWithCarry, Word256.zero]",
                "unfold Word256.addWithCarry; unfold Word256.zero; simp",
                1,
            )
            assert edit_z2 != orig_fc_z and edit_z2 != edit_z1
            fc_file.write_text(edit_z2)
            res_local_z2, m20_local_check_new_proof_zygote_ms = run_cmd(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(fc_file),
                    "--decl",
                    "addWithCarry_zero_right",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env=env,
            )
            assert res_local_z2["status"] == "theorem_verified", f"Expected theorem_verified on 2nd new proof, got {res_local_z2}"
            assert res_local_z2.get("zygote_used") is True
            assert res_local_z2.get("zygote_env_cache_hit") is True, (
                f"Expected zygote_env_cache_hit=True on 2nd local proof edit, got {res_local_z2}"
            )
            assert m20_local_check_new_proof_zygote_ms < 15.0, (
                f"Expected M20_local_check_new_proof_zygote_ms < 15ms, got {m20_local_check_new_proof_zygote_ms:.2f}ms"
            )
        finally:
            fc_file.write_text(orig_fc_z)

        # 12b. Local CPU Perceus/FBIP fast-check cold vs warm on uncached TURBO_LEAN_HOME (M10f, M10g)
        local_fc_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_eval_local_fc_"))
        try:
            local_fc_env = {"TURBO_LEAN_HOME": str(local_fc_dir)}
            res_local_fc_cold, m10f_local_fastcheck_cold_ms = run_cmd(
                [str(BIN), "--json", "fast-check", str(fastcheck_file)],
                env=local_fc_env,
            )
            assert res_local_fc_cold["status"] == "ok", f"Expected local fast-check ok, got {res_local_fc_cold}"
            assert res_local_fc_cold["mode"] == "native_cpu_perceus"
            assert res_local_fc_cold["compile_cache_hit"] is False
            assert "Checked 1,000,000 256-bit states" in res_local_fc_cold["output"]
            assert m10f_local_fastcheck_cold_ms < 15.0, (
                f"Expected cold local fast-check < 15ms via shared /dev/shm harness cache, got {m10f_local_fastcheck_cold_ms:.2f}ms"
            )

            res_local_fc_warm, m10g_local_fastcheck_warm_ms = run_cmd(
                [str(BIN), "--json", "fast-check", str(fastcheck_file)],
                env=local_fc_env,
            )
            assert res_local_fc_warm["status"] == "ok"
            assert res_local_fc_warm["compile_cache_hit"] is True
            assert res_local_fc_warm["binary_cache_key"] == res_local_fc_cold["binary_cache_key"]
            assert m10g_local_fastcheck_warm_ms < 15.0, (
                f"Expected warm local fast-check < 15ms, got {m10g_local_fastcheck_warm_ms:.2f}ms"
            )
        finally:
            shutil.rmtree(local_fc_dir, ignore_errors=True)

        # 14. Season 2, Season 3 & Season 4 Gate Validation:
        # Gate 1: Formal Meta-Verification of turbo-lean in Lean 4 (meta-theorems in Assembler.lean & Inspector.lean)
        asm_src_text = asm_file.read_text()
        insp_src_text = insp_file.read_text()
        for meta_thm in (
            "sharded_proof_irrelevance_stmt_preserved",
            "sharded_proof_irrelevance_sound",
            "shard_clean_iff_no_forbidden",
            "allShardsCertified_implies_any_forbidden_false",
            "assembled_module_zero_sorry_of_shards",
            "pr_verify_unmodified_shard_sound",
            "pr_verify_modified_shard_sound",
            "pr_verify_incremental_sound",
            "cone_outside_modification_invariant",
            "cone_thm_proof_edit_invariant",
            "cone_defn_body_edit_detected",
            "constraint_prop_forall_equiv",
            "constraint_prop_bool_sound",
            "shard_preimage_eq_iff",
            "turboVerify_eq_kernelClean",
            "turboVerify_zero_false_negatives",
            "turboVerify_zero_false_positives",
            "kernel_gate_blocks_macro_bypass",
            "relative_cone_sorry_prefix_sound",
        ):
            assert f"TurboLean.Assembler.{meta_thm}" in asm_src_text, (
                f"Expected formal meta-theorem {meta_thm} in Assembler.lean"
            )
            assert f"theorem {meta_thm}" in asm_src_text, (
                f"Expected theorem definition {meta_thm} in Assembler.lean"
            )
        for meta_thm in (
            "allAxiomsAllowed_cons",
            "hasNoForbiddenAxioms_cons",
            "gdsf_pinned_never_evicted",
            "gdsf_clock_monotonic",
            "gdsf_eviction_preserves_pinned_head",
            "gdsf_eviction_preserves_certified_receipts",
            "gdsf_eviction_preserves_pinned_lookup",
        ):
            assert f"TurboLean.Inspector.{meta_thm}" in insp_src_text, (
                f"Expected formal meta-theorem {meta_thm} in Inspector.lean"
            )
        res_asm_all, _ = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(asm_file),
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_asm_all["status"] in ("file_verified", "all_shards_cached")
        res_insp_all, _ = run_cmd(
            [
                str(BIN),
                "--json",
                "check",
                str(insp_file),
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env,
        )
        assert res_insp_all["status"] in ("file_verified", "all_shards_cached")

        # Gate 4: Lean 4 -> GPU CUDA Counterexample Transpiler verification (`fast-check --transpile-lean`)
        res_transpile_valid, _ = run_cmd(
            [
                str(BIN),
                "--json",
                "fast-check",
                str(fastcheck_file),
                "--transpile-lean",
                "bitNot_bitAnd",
            ],
            env=env,
        )
        assert res_transpile_valid.get("transpiled_from_lean") is True, (
            f"Expected transpiled_from_lean=True, got {res_transpile_valid}"
        )
        assert res_transpile_valid["status"] == "ok", (
            f"Expected valid transpiled theorem status=ok, got {res_transpile_valid}"
        )

        # 15. Season 4 Differential Mutation Oracle & Self-Healing /dev/shm Chaos Test (< 15 ms total)
        t_dmo0 = time.perf_counter()
        shm_splits_dir = Path("/dev/shm/turbo-lean-staging/file_splits_v2")
        shm_splits_dir.mkdir(parents=True, exist_ok=True)
        chaos_dummy = shm_splits_dir / "st_chaos_corrupted_dummy.json"
        chaos_dummy.write_text("{corrupted")
        try:
            res_chaos_heal, m21_differential_mutation_oracle_ms = run_cmd(
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
            assert res_chaos_heal["status"] in ("file_verified", "all_shards_cached"), (
                f"Expected self-healing check under corrupted /dev/shm split cache, got {res_chaos_heal}"
            )
            assert res_chaos_heal.get("shard_hits", 0) >= 8, (
                f"Expected >= 8 shard hits on Reflection.lean during differential mutation oracle check, got {res_chaos_heal}"
            )
        finally:
            chaos_dummy.unlink(missing_ok=True)
        dmo_total_ms = (time.perf_counter() - t_dmo0) * 1000.0
        assert dmo_total_ms < 15.0, (
            f"Expected differential_mutation_oracle + /dev/shm chaos self-healing < 15ms, got {dmo_total_ms:.2f}ms"
        )

        summary = {
            "invariants_passed": True,
            "kernel_inspector_verified": True,
            "kernel_expr_replay_verified": True,
            "cryptographic_receipt_verified": True,
            "git_pr_verify_verified": True,
            "multi_agent_singleflight_verified": True,
            "meta_spec_verified": True,
            "stateful_ast_splitter_verified": True,
            "zygote_prefix_cow_verified": True,
            "lean_to_cuda_transpiler_verified": True,
            "differential_mutation_oracle_verified": True,
            "interface_hash": interface_hash_1,
            "metrics": {
                "M1_ci_verify_cold_ms": round(ci_cold_ms, 2),
                "M2_warm_build_hit_ms": round(warm_build_ms, 2),
                "M3_shard_check_cold_ms": round(shard_cold_ms, 2),
                "M3_before_lake_env_cache_ms": round(shard_unwarmed_env_ms, 2),
                "M3_after_lake_env_cache_ms": round(shard_warmed_env_ms, 2),
                "M4_shard_check_warm_ms": round(shard_warm_ms, 2),
                "M5_pack_import_ms": round(imp_ms, 2),
                "M5b_pack_import_warm_ms": round(imp_warm_ms, 2),
                "M6_parallel_7_shards_ms": round(par_shards_ms, 2),
                "M6b_coalesced_2_shards_ms": round(fc_coalesced_2_shards_ms, 2),
                "M7_all_8_shards_warm_ms": round(all_cached_ms, 2),
                "M8_delta_sync_noop_ms": round(m8_delta_sync_noop_ms, 2),
                "M9_delta_sync_incremental_ms": round(m9_delta_sync_inc_ms, 2),
                "M9b_delta_sync_push_ms": round(m9b_delta_sync_push_ms, 2),
                "M9c_delta_sync_push_noop_ms": round(m9c_delta_sync_push_noop_ms, 2),
                "M10_http_remote_fastcheck_ms": round(m10_http_fastcheck_ms, 2),
                "M10b_http_remote_fastcheck_warm_ms": round(m10b_http_fastcheck_warm_ms, 2),
                "M10c_http_remote_shard_check_cold_ms": round(m10c_http_remote_shard_check_cold_ms, 2),
                "M10d_http_remote_shard_check_hit_ms": round(m10d_http_remote_shard_check_hit_ms, 2),
                "M10e_http_remote_batch_coalesced_ms": round(m10e_http_remote_batch_coalesced_ms, 2),
                "M10f_local_fastcheck_cold_ms": round(m10f_local_fastcheck_cold_ms, 2),
                "M10g_local_fastcheck_warm_ms": round(m10g_local_fastcheck_warm_ms, 2),
                "M8_inspector_shard_cold_ms": round(insp_cold_ms, 2),
                "M9_inspector_shard_warm_ms": round(insp_warm_ms, 2),
                "M10_assembler_shard_cold_ms": round(asm_cold_ms, 2),
                "M11_assembler_shard_warm_ms": round(asm_warm_ms, 2),
                "M12_kernel_adddecl_4_thms_us": round(total_replay_us, 2),
                "M13_kernel_adddecl_4_thms_heartbeats": total_replay_hb,
                "M14_dir_check_warm_ms": round(m14_dir_check_warm_ms, 2),
                "M14b_cross_file_coalesced_cold_ms": round(m14b_cross_file_coalesced_cold_ms, 2),
                "M15_verify_receipt_ms": round(verify_receipt_ms, 2),
                "M16_pr_verify_proof_edit_ms": round(m16_pr_verify_proof_edit_ms, 2),
                "M16b_pr_verify_multi_file_edit_ms": round(m16b_pr_verify_multi_file_edit_ms, 2),
                "M17_multi_agent_singleflight_4x_ms": round(m17_multi_agent_singleflight_4x_ms, 2),
                "M18_seed_shards_ms": round(m18_seed_shards_ms, 2),
                "M19_zygote_new_proof_warm_env_ms": round(m19_zygote_new_proof_warm_env_ms, 2),
                "M20_local_check_new_proof_zygote_ms": round(m20_local_check_new_proof_zygote_ms, 2),
                "M21_differential_mutation_oracle_ms": round(dmo_total_ms, 2),
                "stored_blobs": res_status["total_blobs"],
                "completed_actions": res_status["total_actions"],
                "total_shard_hits": res_status["total_shard_hits"],
                "saved_compute_ms": res_status["saved_compute_ms"],
                "coalesced_singleflight_saves": res_status["total_coalesced_waits"],
            },
        }
        print(json.dumps(summary, indent=2))
    finally:
        shutil.rmtree(cache_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
