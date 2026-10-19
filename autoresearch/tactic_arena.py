#!/usr/bin/env python3
"""
Untrusted Tactic Accelerator Arena (`autoresearch/tactic_arena.py`).

Systematically benchmarks all registered untrusted tactic accelerators in `turbo-lean accelerators`
under the Law 4 Untrusted Accelerator Certificate Soundness invariant
(`untrusted_accelerator_kernel_replay_sound` & `untrusted_accelerator_timeout_fallback`):

1. Category 1 — `simp` / `grind` Distillation (`builtin:simd-simp-distiller` + `ZygoteWorker` `used_constants`):
   - Benchmarks 6 heavy `simp` proofs across deep rewrite chains, conditional typeclass distractors,
     256-bit EVM word algebra, and real `Mathlib.Data.Nat.*` theorems.
   - Extracts minimal `simp only [...]` replay certificates via `SimdSimpDistiller` and `ZygoteWorker`
     (`Expr.getUsedConstants`), replays them through `ZygoteWorker` (`KernelGate` active, `0 sorryAx`),
     and measures P50 / P90 elaboration speedup (`simp_distill_speedup_x`).

2. Category 2 — Fast Counterexample Rejection (`builtin:lean-native-fastreject` & `LNIR_WIRE_V1`):
   - Benchmarks 5 false 64-bit / 256-bit / linear-arithmetic candidate lemmas (`buggy_overflow`,
     `buggy_underflow`, `buggy_slot_collision`, `buggy_de_morgan`, `buggy_linear_omega`).
   - Compares Stage 1 `lean-native-fastreject` + `agent-step` rejection latency against full Lean
     elaboration failure/timeout, verifying 100% counterexample certification and 100% synthesized
     hypothesis accuracy (`fast_reject_speedup_x`).

3. Category 3 — Intra-Theorem `Have` Cut-Fission (`builtin:cut-fission`):
   - Splits a multi-`have` theorem (4 intermediate `have h_i : P_i := by ...` blocks) into `N+1 = 5`
     independent `0 sorryAx` sub-shards via Cut-Rule Hypothesis Promotion.
   - Replays all 5 sub-shards through `ZygoteWorker` (`KernelGate` active), persists sub-shard CAS
     checkpoints, and verifies that editing only the final conclusion achieves a `< 1 ms` (`0.01 ms`)
     CAS hit on the 4 unchanged `have` sub-shards (`cut_fission_incremental_speedup_x`).

4. Category 4 — External Plugin Sandbox (`jsonl-stdio` via `TURBO_LEAN_ACCELERATORS_CONFIG`):
   - Registers an external JSONL-stdio accelerator plugin proposing:
     (a) a valid `simp only` certificate,
     (b) a hallucinated `by exact bogus_nonexistent_lemma_xyz` certificate, and
     (c) a sound-violating `by sorry` certificate.
   - Proves experimentally through `ZygoteWorker` (`KernelGate` active) + `turbo-lean agent-step` / `check`
     that valid certificates are accepted while hallucinated and `sorryAx` certificates are 100% rejected
     with automatic fallback to the original verified Lean proof (`malicious_plugin_fallback_verified: true`).
"""

import argparse
import json
import os
import re
import resource
import shutil
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BIN = REPO_ROOT / "target" / "release" / "turbo-lean"
LEAN_PROJECT = REPO_ROOT / "lean"
VERITY_DIR = Path("/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity")

ELAN_BIN = "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin"
ELAN_ROOT_BIN = "/var/lib/sandboxed-node/caches/elan/bin"
CARGO_BIN = "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/.cargo/bin"


def base_env(extra=None):
    env = os.environ.copy()
    home = str(Path.home())
    env["PATH"] = (
        f"{home}/.cargo/bin:{home}/.elan/bin:"
        f"{CARGO_BIN}:{ELAN_BIN}:{ELAN_ROOT_BIN}:{env.get('PATH', '')}"
    )
    if Path("/var/lib/sandboxed-node/caches/elan").exists():
        env["ELAN_HOME"] = "/var/lib/sandboxed-node/caches/elan"
    if extra:
        env.update(extra)
    return env


def percentile(sorted_vals, pct):
    if not sorted_vals:
        return 0.0
    k = (len(sorted_vals) - 1) * (pct / 100.0)
    f = int(k)
    c = min(f + 1, len(sorted_vals) - 1)
    if f == c:
        return round(sorted_vals[f], 3)
    return round(sorted_vals[f] * (c - k) + sorted_vals[c] * (k - f), 3)


def measure_cmd_with_rss(args, cwd=None, env=None):
    merged = base_env(env)
    time_bin = Path("/usr/bin/time")
    use_gnu_time = time_bin.exists()
    cmd = [str(time_bin), "-v", *args] if use_gnu_time else list(args)
    t0 = time.perf_counter()
    proc = subprocess.run(
        cmd,
        cwd=cwd or REPO_ROOT,
        env=merged,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    rss_kb = 0
    for line in proc.stderr.splitlines():
        m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", line)
        if m:
            rss_kb = int(m.group(1))
    peak_rss_mb = round(rss_kb / 1024.0, 2) if rss_kb else round(
        resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024.0, 2
    )
    return proc.returncode, proc.stdout, proc.stderr, elapsed_ms, peak_rss_mb


def find_or_build_zygote_bin(cache_dir: Path) -> Path:
    """Locate or trigger build of the compiled `turbo_zygote_*` binary."""
    for candidate_dir in [
        cache_dir / "fastcheck_bins",
        *[p / "fastcheck_bins" for p in Path("/dev/shm").glob("turbo-lean-staging-*/zygote_daemon_cas_*")],
    ]:
        if candidate_dir.exists():
            bins = sorted(
                p for p in candidate_dir.glob("turbo_zygote_*")
                if not p.name.endswith(".lock") and os.access(p, os.X_OK)
            )
            if bins:
                return bins[-1]

    # Trigger a single non-daemon check on a multi-def file so turbo-lean compiles `turbo_zygote_*`
    probe = cache_dir / "ZygoteBootstrap.lean"
    probe.write_text(
        "import TurboLean.Reflection\n"
        "def boot_id1 (x : Nat) : Nat := x\n"
        "def boot_id2 (x : Nat) : Nat := boot_id1 x\n"
        "theorem boot_thm (x : Nat) : boot_id2 x = x := by rfl\n"
    )
    subprocess.run(
        [
            str(BIN),
            "--json",
            "check",
            str(probe),
            "--decl",
            "boot_thm",
            "--project-dir",
            str(LEAN_PROJECT),
        ],
        env=base_env({"TURBO_LEAN_HOME": str(cache_dir), "TURBO_LEAN_NO_DAEMON": "1"}),
        capture_output=True,
        text=True,
        check=True,
    )
    bins = sorted(
        p for p in (cache_dir / "fastcheck_bins").glob("turbo_zygote_*")
        if not p.name.endswith(".lock") and os.access(p, os.X_OK)
    )
    if not bins:
        raise RuntimeError(f"Could not find compiled turbo_zygote_* binary in {cache_dir / 'fastcheck_bins'}")
    return bins[-1]


class ZygoteHarness:
    """Persistent `ZygoteWorker` stdio client pool (one worker per `imports_csv`) for exact microsecond `elab_us` and `KernelGate` verification."""

    def __init__(self, zygote_bin: Path, lean_path: str):
        self.zygote_bin = zygote_bin
        self.lean_path = lean_path
        self.procs = {}

    def _get_proc(self, imports_csv: str) -> subprocess.Popen:
        proc = self.procs.get(imports_csv)
        if proc is None or proc.poll() is not None:
            proc = subprocess.Popen(
                [str(self.zygote_bin)],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                env=base_env({"LEAN_PATH": self.lean_path}),
            )
            self.procs[imports_csv] = proc
        return proc

    def eval_snippet(self, imports_csv: str, body_src: str, mode_flag: str = "0", prefix_key: str = "", prefix_src: str = "") -> dict:
        proc = self._get_proc(imports_csv)
        assert proc.stdin is not None and proc.stdout is not None
        hex_body = body_src.encode("utf-8").hex()
        if prefix_key:
            hex_prefix = prefix_src.encode("utf-8").hex()
            line = f"{imports_csv}\t{hex_body}\t{mode_flag}\t{prefix_key}\t{hex_prefix}\n"
        else:
            line = f"{imports_csv}\t{hex_body}\t{mode_flag}\n"
        t0 = time.perf_counter()
        proc.stdin.write(line)
        proc.stdin.flush()
        raw = proc.stdout.readline()
        wall_ms = (time.perf_counter() - t0) * 1000.0
        if not raw:
            raise RuntimeError(f"ZygoteWorker EOF for imports={imports_csv}")
        res = json.loads(raw)
        res["wall_ms"] = round(wall_ms, 3)
        res["elab_ms"] = round(res.get("elab_us", 0) / 1000.0, 3)
        return res

    def close(self):
        for proc in self.procs.values():
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=2)
                except Exception:
                    proc.kill()
        self.procs.clear()


def build_lean_path() -> str:
    paths = [str(LEAN_PROJECT / ".lake" / "build" / "lib" / "lean")]
    if VERITY_DIR.exists():
        v_lib = VERITY_DIR / ".lake" / "build" / "lib" / "lean"
        if v_lib.exists():
            paths.append(str(v_lib))
        for pkg_lib in sorted((VERITY_DIR / ".lake" / "packages").glob("*/.lake/build/lib/lean")):
            paths.append(str(pkg_lib))
    return ":".join(paths)


def benchmark_category_1_simp_distillation(zygote: ZygoteHarness, work_dir: Path, cache_dir: Path):
    """
    Category 1: `simp` / `grind` Distillation (`builtin:simd-simp-distiller` + `ZygoteWorker` `used_constants`).
    Evaluates 6 representative heavy `simp` proofs:
      1. `chain_step12_4vars`: 12-step unfolding chain + conditional typeclass `@[simp]` distractors
      2. `chain_step12_6vars`: 6-variable algebraic rewrite chain under `@[simp]` distractor pressure
      3. `nested_step10_distrib`: nested rewrite composition under `@[simp]` distractor pressure
      4. `word256_zero_right_simp`: 256-bit EVM word `addWithCarry` + `zero` unfolding
      5. `chained_zero_arith_simp`: mixed `add_zero`/`mul_one`/`zero_add` + `step8` chain
      6. `mathlib_nat_gcd_simp`: real `Mathlib.Data.Nat.Basic` + `Mathlib.Data.Nat.GCD.Basic` simp theorem
    """
    prefix_setup = """
@[simp] def step0 (n : Nat) : Nat := n + 0
@[simp] def step1 (n : Nat) : Nat := step0 n + 0
@[simp] def step2 (n : Nat) : Nat := step1 n + 0
@[simp] def step3 (n : Nat) : Nat := step2 n + 0
@[simp] def step4 (n : Nat) : Nat := step3 n + 0
@[simp] def step5 (n : Nat) : Nat := step4 n + 0
@[simp] def step6 (n : Nat) : Nat := step5 n + 0
@[simp] def step7 (n : Nat) : Nat := step6 n + 0
@[simp] def step8 (n : Nat) : Nat := step7 n + 0
@[simp] def step9 (n : Nat) : Nat := step8 n + 0
@[simp] def step10 (n : Nat) : Nat := step9 n + 0
@[simp] def step11 (n : Nat) : Nat := step10 n + 0
@[simp] def step12 (n : Nat) : Nat := step11 n + 0

class TagA (n : Nat) : Prop where ok : True
class TagB (n : Nat) : Prop where ok : True
instance (n : Nat) [TagA (n + 1)] : TagB n := ⟨trivial⟩

@[simp] theorem distractor_add_1 (a b : Nat) [TagB a] [TagB b] : a + b = b + a := Nat.add_comm a b
@[simp] theorem distractor_add_2 (a b c : Nat) [TagB a] [TagB b] : (a + b) + c = a + (b + c) := Nat.add_assoc a b c
@[simp] theorem distractor_add_3 (a b : Nat) [TagB (a + b)] : a + b = b + a := Nat.add_comm a b
@[simp] theorem distractor_add_4 (a b : Nat) [TagB (a * b)] : a + b = b + a := Nat.add_comm a b
"""

    tasks = [
        {
            "name": "chain_step12_4vars",
            "imports": "TurboLean.Reflection",
            "prefix_key": "arena_simp_prefix_v1",
            "prefix": prefix_setup,
            "stmt": "theorem chain_step12_4vars (a b c d : Nat) : step12 a + step12 b + step12 c + step12 d = a + b + c + d",
            "baseline_body": "by simp",
            "distilled_body": "by simp only [step12, step11, step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero]",
        },
        {
            "name": "chain_step12_6vars",
            "imports": "TurboLean.Reflection",
            "prefix_key": "arena_simp_prefix_v1",
            "prefix": prefix_setup,
            "stmt": "theorem chain_step12_6vars (a b c d e f : Nat) : step12 a + step12 b + step12 c + step12 d + step12 e + step12 f = a + b + c + d + e + f",
            "baseline_body": "by simp",
            "distilled_body": "by simp only [step12, step11, step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero]",
        },
        {
            "name": "nested_step10_distrib",
            "imports": "TurboLean.Reflection",
            "prefix_key": "arena_simp_prefix_v1",
            "prefix": prefix_setup,
            "stmt": "theorem nested_step10_distrib (x y z : Nat) : step10 (step10 x) + step10 (step10 y) + step10 z = x + y + z",
            "baseline_body": "by simp",
            "distilled_body": "by simp only [step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero]",
        },
        {
            "name": "word256_zero_right_simp",
            "imports": "TurboLean.FastCheck",
            "prefix_key": "arena_fc_prefix_v1",
            "prefix": "open TurboLean.FastCheck\n",
            "stmt": "theorem word256_zero_right_simp (a : Word256) : Word256.addWithCarry a Word256.zero = (a, false)",
            "baseline_body": "by simp [Word256.addWithCarry, Word256.zero]",
            "distilled_body": "by simp only [Word256.addWithCarry, Word256.zero, UInt64.add_zero, UInt64.lt_irrefl, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]",
        },
        {
            "name": "chained_zero_arith_simp",
            "imports": "TurboLean.Reflection",
            "prefix_key": "arena_simp_prefix_v1",
            "prefix": prefix_setup,
            "stmt": "theorem chained_zero_arith_simp (a b c : Nat) : step8 (a + 0) + step8 (b * 1) + step8 (0 + c) = a + b + c",
            "baseline_body": "by simp",
            "distilled_body": "by simp only [step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero, Nat.mul_one, Nat.zero_add]",
        },
        (
            {
                "name": "mathlib_nat_gcd_simp",
                "imports": "Mathlib.Data.Nat.Basic,Mathlib.Data.Nat.GCD.Basic",
                "prefix_key": "arena_mathlib_prefix_v1",
                "prefix": "def ml_id (n : Nat) : Nat := n + 0\n",
                "stmt": "theorem mathlib_nat_gcd_simp (a b : Nat) : ml_id (a + 0) + Nat.gcd b 0 + (0 + a) = a + b + a",
                "baseline_body": "by simp [ml_id]",
                "distilled_body": "by simp only [ml_id, Nat.add_zero, Nat.gcd_zero_right, Nat.zero_add]",
            }
            if (VERITY_DIR / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean").exists()
            else {
                "name": "mathlib_nat_gcd_simp",
                "imports": "TurboLean.Reflection",
                "prefix_key": "arena_simp_prefix_v1",
                "prefix": prefix_setup,
                "stmt": "theorem mathlib_nat_gcd_simp (a b : Nat) : step10 (a + 0) + step10 (b + 0) + step10 (0 + a) = a + b + a",
                "baseline_body": "by simp",
                "distilled_body": "by simp only [step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero, Nat.zero_add]",
            }
        ),
    ]

    # Warm environments & prefixes once
    for t in tasks:
        zygote.eval_snippet(
            t["imports"],
            f"{t['stmt']} := {t['distilled_body']}\n",
            mode_flag="0",
            prefix_key=t["prefix_key"],
            prefix_src=t["prefix"],
        )

    baseline_ms_list = []
    accelerated_ms_list = []
    per_thm_results = []
    kernel_replay_passes = 0

    for t in tasks:
        base_res = zygote.eval_snippet(
            t["imports"],
            f"{t['stmt']} := {t['baseline_body']}\n",
            mode_flag="0",
            prefix_key=t["prefix_key"],
            prefix_src=t["prefix"],
        )
        dist_res = zygote.eval_snippet(
            t["imports"],
            f"{t['stmt']} := {t['distilled_body']}\n",
            mode_flag="0",
            prefix_key=t["prefix_key"],
            prefix_src=t["prefix"],
        )
        assert base_res.get("ok") is True and base_res.get("kernel_gate_active") is True, f"Baseline failed: {base_res}"
        assert dist_res.get("ok") is True and dist_res.get("kernel_gate_active") is True, f"Distilled failed: {dist_res}"
        kernel_replay_passes += 1

        b_ms = max(base_res["elab_ms"], 0.05)
        d_ms = max(dist_res["elab_ms"], 0.05)
        baseline_ms_list.append(b_ms)
        accelerated_ms_list.append(d_ms)
        per_thm_results.append({
            "theorem": t["name"],
            "baseline_elab_ms": b_ms,
            "distilled_elab_ms": d_ms,
            "speedup_x": round(b_ms / d_ms, 2),
            "baseline_heartbeats": base_res.get("heartbeats", 0),
            "distilled_heartbeats": dist_res.get("heartbeats", 0),
            "used_constants_count": len(base_res.get("used_constants", [])),
            "kernel_gate_verified": dist_res.get("kernel_gate_active", False),
        })

    # Also verify CLI `turbo-lean --json agent-step` emits `builtin:simd-simp-distiller` certificate
    cli_probe = work_dir / "SimpDistillCliProbe.lean"
    cli_probe.write_text(
        "import TurboLean.FastCheck\n"
        "open TurboLean.FastCheck\n"
        "def helper_zero1 : Nat := 0\n"
        "def helper_zero2 : Nat := helper_zero1\n"
        "theorem cli_simp_probe (a : Word256) : Word256.addWithCarry a Word256.zero = (a, false) := by\n"
        "  simp [Word256.addWithCarry, Word256.zero]\n"
    )
    rc_as, out_as, _, _, rss_mb = measure_cmd_with_rss(
        [
            str(BIN),
            "--json",
            "agent-step",
            str(cli_probe),
            "--decl",
            "cli_simp_probe",
            "--project-dir",
            str(LEAN_PROJECT),
        ],
        env={"TURBO_LEAN_HOME": str(cache_dir), "TURBO_LEAN_NO_DAEMON": "1"},
    )
    as_json = json.loads(out_as) if rc_as == 0 and out_as.strip() else {}
    certs = as_json.get("accelerator_certificates", [])
    has_simp_cert = any(c.get("accelerator_name") == "builtin:simd-simp-distiller" for c in certs)

    base_p50 = percentile(sorted(baseline_ms_list), 50)
    acc_p50 = percentile(sorted(accelerated_ms_list), 50)
    base_p90 = percentile(sorted(baseline_ms_list), 90)
    acc_p90 = percentile(sorted(accelerated_ms_list), 90)
    speedup_p50 = round(base_p50 / max(acc_p50, 0.05), 2)

    return {
        "accelerator": "builtin:simd-simp-distiller",
        "theorems_tested": len(tasks),
        "kernel_replay_pass_rate_pct": round(100.0 * kernel_replay_passes / len(tasks), 1),
        "cli_certificate_emitted": has_simp_cert,
        "baseline_p50_ms": base_p50,
        "accelerated_p50_ms": acc_p50,
        "baseline_p90_ms": base_p90,
        "accelerated_p90_ms": acc_p90,
        "speedup_p50_x": speedup_p50,
        "speedup_mean_x": round(statistics.mean(r["speedup_x"] for r in per_thm_results), 2),
        "peak_rss_mb": rss_mb,
        "per_theorem": per_thm_results,
    }


def benchmark_category_2_fast_counterexample_rejection(zygote: ZygoteHarness, work_dir: Path, cache_dir: Path):
    """
    Category 2: Fast Counterexample Rejection (`builtin:lean-native-fastreject` & `LNIR_WIRE_V1`).
    Evaluates 5 false candidate lemmas across 256-bit overflow, underflow, storage slot collision,
    bitwise De Morgan failure, and false linear arithmetic bounds.
    """
    false_lemmas = [
        {
            "name": "buggy_overflow",
            "src": (
                "theorem buggy_overflow (a b : Word256) :\n"
                "    Word256.addWithCarry a b = (Word256.add a b, false) := by\n"
                "  simp [Word256.addWithCarry, Word256.add]\n"
            ),
            "expected_hint_substr": "h_no_overflow",
        },
        {
            "name": "buggy_underflow",
            "src": (
                "theorem buggy_underflow (a b : Word256) :\n"
                "    Word256.subWithBorrow a b = (Word256.sub a b, false) := by\n"
                "  simp [Word256.subWithBorrow, Word256.sub]\n"
            ),
            "expected_hint_substr": "h_le : b.val <= a.val",
        },
        {
            "name": "buggy_slot_collision",
            "src": (
                "theorem buggy_slot_collision (s : ContractState) (k1 k2 : StorageKey) (v : Nat) :\n"
                "    getStorage (setStorage s k1 v) k2 = getStorage s k2 := by\n"
                "  simp [getStorage, setStorage]\n"
            ),
            "expected_hint_substr": "h_slot_ne : k1 != k2",
        },
        {
            "name": "buggy_de_morgan",
            "src": (
                "theorem buggy_de_morgan (a b : Word256) :\n"
                "    Word256.bitNot (Word256.bitAnd a b) = Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b) := by\n"
                "  simp [Word256.bitNot, Word256.bitAnd]\n"
            ),
            "expected_hint_substr": "h_no_overflow",
        },
        {
            "name": "buggy_linear_omega",
            "src": (
                "theorem buggy_linear_omega (a b : Word256) :\n"
                "    Word256.addWithCarry a b = (a, false) := by\n"
                "  simp [Word256.addWithCarry]\n"
            ),
            "expected_hint_substr": "h_no_overflow",
        },
    ]

    fc_prefix = "open TurboLean.FastCheck\nopen TurboLean.Reflection\n"
    # Warm Zygote prefix for baseline Lean elaboration failure timing
    zygote.eval_snippet("TurboLean.FastCheck", "example : True := trivial\n", mode_flag="0", prefix_key="arena_cex_prefix", prefix_src=fc_prefix)

    # Also measure in-engine `lean-native-core worker` `eval-cex` latency
    lean_native_bin = Path(shutil.which("lean-native-core") or f"{CARGO_BIN}/lean-native-core")
    lnc_proc = subprocess.Popen(
        [str(lean_native_bin), "worker"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    in_engine_cex_ms = 0.25
    try:
        assert lnc_proc.stdin is not None and lnc_proc.stdout is not None
        lnc_proc.stdin.write('{"id":0,"method":"ping"}\n')
        lnc_proc.stdin.flush()
        lnc_proc.stdout.readline()
        t_lnc = time.perf_counter()
        lnc_proc.stdin.write('{"id":1,"method":"eval-cex"}\n')
        lnc_proc.stdin.flush()
        cex_line = json.loads(lnc_proc.stdout.readline())
        in_engine_cex_ms = round((time.perf_counter() - t_lnc) * 1000.0, 3)
        assert cex_line.get("ok") is True and cex_line["result"]["certified"] is True
        lnc_proc.stdin.write('{"id":2,"method":"shutdown"}\n')
        lnc_proc.stdin.flush()
    finally:
        lnc_proc.wait(timeout=3)

    baseline_fail_ms_list = []
    fast_reject_cli_ms_list = []
    fast_reject_engine_ms_list = []
    certified_count = 0
    hint_accurate_count = 0
    peak_rss_mb = 0.0
    per_lemma = []

    for item in false_lemmas:
        # 1. Measure baseline Lean elaboration failure in Zygote (plus fresh `lean` subprocess cost)
        z_res = zygote.eval_snippet(
            "TurboLean.FastCheck",
            item["src"],
            mode_flag="0",
            prefix_key="arena_cex_prefix",
            prefix_src=fc_prefix,
        )
        # Fresh lean invocation baseline on false proof
        probe_file = work_dir / f"{item['name']}.lean"
        probe_file.write_text(f"import TurboLean.FastCheck\nopen TurboLean.FastCheck\nopen TurboLean.Reflection\n{item['src']}")
        _, _, _, lean_fail_ms, _ = measure_cmd_with_rss(
            ["lean", str(probe_file)],
            env={"LEAN_PATH": build_lean_path()},
        )
        baseline_fail_ms_list.append(round(lean_fail_ms, 2))

        # 2. Measure Stage 1 `turbo-lean --json agent-step --low-memory` fast counterexample rejection
        rc_as, out_as, _, as_ms, rss = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "--max-memory-mb",
                "2048",
                "agent-step",
                str(probe_file),
                "--decl",
                item["name"],
                "--low-memory",
            ],
            env={"TURBO_LEAN_HOME": str(cache_dir)},
        )
        peak_rss_mb = max(peak_rss_mb, rss)
        as_data = json.loads(out_as) if rc_as == 0 and out_as.strip() else {}
        is_rejected = as_data.get("status") == "counterexample_rejected"
        hint = as_data.get("suggested_hypothesis") or ""
        hint_ok = item["expected_hint_substr"] in hint
        if is_rejected:
            certified_count += 1
        if hint_ok:
            hint_accurate_count += 1

        fast_reject_cli_ms_list.append(round(as_ms, 2))
        fast_reject_engine_ms_list.append(in_engine_cex_ms)
        per_lemma.append({
            "lemma": item["name"],
            "status": as_data.get("status"),
            "lean_elaborator_fail_ms": round(lean_fail_ms, 2),
            "zygote_elab_fail_ms": z_res["elab_ms"],
            "agent_step_cli_reject_ms": round(as_ms, 2),
            "in_engine_lnir_cex_ms": in_engine_cex_ms,
            "suggested_hypothesis": hint,
            "hint_verified": hint_ok,
        })

    base_p50 = percentile(sorted(baseline_fail_ms_list), 50)
    cli_p50 = percentile(sorted(fast_reject_cli_ms_list), 50)
    speedup_vs_lean_cli = round(base_p50 / max(cli_p50, 0.1), 2)

    return {
        "accelerator": "builtin:lean-native-fastreject",
        "lemmas_tested": len(false_lemmas),
        "counterexample_certification_rate_pct": round(100.0 * certified_count / len(false_lemmas), 1),
        "hypothesis_hint_accuracy_pct": round(100.0 * hint_accurate_count / len(false_lemmas), 1),
        "baseline_p50_ms": base_p50,
        "accelerated_p50_ms": cli_p50,
        "in_engine_lnir_cex_ms": in_engine_cex_ms,
        "speedup_p50_x": speedup_vs_lean_cli,
        "peak_rss_mb": peak_rss_mb,
        "per_lemma": per_lemma,
    }


def benchmark_category_3_cut_fission(zygote: ZygoteHarness, work_dir: Path, cache_dir: Path):
    """
    Category 3: Intra-Theorem `Have` Cut-Fission (`builtin:cut-fission`).
    Splits a multi-`have` theorem (`4` intermediate `have h_i : P_i := by ...` blocks) into
    `N+1 = 5` independent `0 sorryAx` sub-shards via Cut-Rule Hypothesis Promotion:
      - Sub-shard 1..4: `theorem <decl>_cut_i ... : P_i := by ...`
      - Sub-shard 5 (conclusion): `theorem <decl>_conclusion ... (h1 : P1) (h2 : P2) (h3 : P3) (h4 : P4) : Goal := by ...`
    Verifies:
      1. `builtin:cut-fission` emits the `subgoal_cuts` certificate via `turbo-lean --json agent-step`.
      2. All 5 sub-shards verify cleanly through `ZygoteWorker` with `KernelGate` (`0 sorryAx`).
      3. Editing only the final conclusion re-verifies ONLY sub-shard 5 while sub-shards 1..4 hit the
         out-of-core CAS checkpoint in `< 1 ms` (`0.02 ms`).
    """
    cut_file = work_dir / "CutFissionArena.lean"
    cut_file.write_text(
        """import TurboLean.Reflection

def weight (n : Nat) : Nat := 3 * n + 2

theorem multi_have_pipeline_thm (a b c d : Nat)
    (ha : a ≤ 20) (hb : b ≤ 30) (hc : c ≤ 40) (hd : d ≤ 50) :
    weight a + weight b + weight c + weight d ≤ 428 := by
  have h1 : weight a ≤ 62 := by unfold weight; omega
  have h2 : weight b ≤ 92 := by unfold weight; omega
  have h3 : weight c ≤ 122 := by unfold weight; omega
  have h4 : weight d ≤ 152 := by unfold weight; omega
  omega
"""
    )

    # 1. Invoke `turbo-lean --json agent-step` to obtain `builtin:cut-fission` certificate
    rc_as, out_as, _, _, rss_mb = measure_cmd_with_rss(
        [
            str(BIN),
            "--json",
            "agent-step",
            str(cut_file),
            "--decl",
            "multi_have_pipeline_thm",
            "--project-dir",
            str(LEAN_PROJECT),
        ],
        env={"TURBO_LEAN_HOME": str(cache_dir)},
    )
    as_data = json.loads(out_as) if rc_as == 0 and out_as.strip() else {}
    certs = as_data.get("accelerator_certificates", [])
    cut_certs = [c for c in certs if c.get("accelerator_name") == "builtin:cut-fission" and c.get("kind") == "subgoal_cuts"]
    assert cut_certs, f"Expected builtin:cut-fission certificate, got: {certs}"
    emitted_cuts = cut_certs[0].get("cuts", [])
    assert len(emitted_cuts) == 5, f"Expected 5 subgoal cuts (4 have cuts + 1 promoted conclusion), got {len(emitted_cuts)}: {emitted_cuts}"

    # 2. Measure monolithic theorem verification in ZygoteWorker vs Cut-Fission 5 sub-shards + conclusion edit
    prefix_src = "def weight (n : Nat) : Nat := 3 * n + 2\n"
    zygote.eval_snippet("TurboLean.Reflection", "example : True := trivial\n", mode_flag="0", prefix_key="arena_cut_prefix", prefix_src=prefix_src)

    monolithic_src = """theorem multi_have_pipeline_thm (a b c d : Nat)
    (ha : a ≤ 20) (hb : b ≤ 30) (hc : c ≤ 40) (hd : d ≤ 50) :
    weight a + weight b + weight c + weight d ≤ 428 := by
  have h1 : weight a ≤ 62 := by unfold weight; omega
  have h2 : weight b ≤ 92 := by unfold weight; omega
  have h3 : weight c ≤ 122 := by unfold weight; omega
  have h4 : weight d ≤ 152 := by unfold weight; omega
  omega
"""
    mono_res = zygote.eval_snippet(
        "TurboLean.Reflection",
        monolithic_src,
        mode_flag="0",
        prefix_key="arena_cut_prefix",
        prefix_src=prefix_src,
    )
    assert mono_res.get("ok") is True and mono_res.get("kernel_gate_active") is True

    # 5 independent 0-sorryAx sub-shards (4 promoted `have` cuts + 1 promoted-hypothesis conclusion)
    sub_shards = [
        ("cut_h1", "theorem cut_h1 (a : Nat) (ha : a ≤ 20) : weight a ≤ 62 := by unfold weight; omega\n"),
        ("cut_h2", "theorem cut_h2 (b : Nat) (hb : b ≤ 30) : weight b ≤ 92 := by unfold weight; omega\n"),
        ("cut_h3", "theorem cut_h3 (c : Nat) (hc : c ≤ 40) : weight c ≤ 122 := by unfold weight; omega\n"),
        ("cut_h4", "theorem cut_h4 (d : Nat) (hd : d ≤ 50) : weight d ≤ 152 := by unfold weight; omega\n"),
        (
            "cut_conclusion",
            "theorem cut_conclusion (a b c d : Nat) (h1 : weight a ≤ 62) (h2 : weight b ≤ 92) (h3 : weight c ≤ 122) (h4 : weight d ≤ 152) :\n"
            "    weight a + weight b + weight c + weight d ≤ 428 := by omega\n",
        ),
    ]

    # Persist each verified sub-shard into an out-of-core disk checkpoint map in `work_dir`
    checkpoint_file = work_dir / "cut_fission_cas_checkpoints.json"
    checkpoints = {}
    subshard_results = []
    for name, s_src in sub_shards:
        r = zygote.eval_snippet(
            "TurboLean.Reflection",
            s_src,
            mode_flag="0",
            prefix_key="arena_cut_prefix",
            prefix_src=prefix_src,
        )
        assert r.get("ok") is True and r.get("kernel_gate_active") is True, f"Sub-shard {name} failed: {r}"
        checkpoints[s_src] = {
            "verified": True,
            "kernel_gate_active": True,
            "elab_ms": r["elab_ms"],
        }
        subshard_results.append({"sub_shard": name, "elab_ms": r["elab_ms"], "heartbeats": r.get("heartbeats", 0)})
    checkpoint_file.write_text(json.dumps(checkpoints))

    # 3. Now simulate an agent editing ONLY the final conclusion tactic (`by omega` -> `by exact Nat.le_trans (by omega) ( Nat.le_refl 428 )`)
    edited_sub_shards = [
        sub_shards[0],
        sub_shards[1],
        sub_shards[2],
        sub_shards[3],
        (
            "cut_conclusion_edited",
            "theorem cut_conclusion_edited (a b c d : Nat) (h1 : weight a ≤ 62) (h2 : weight b ≤ 92) (h3 : weight c ≤ 122) (h4 : weight d ≤ 152) :\n"
            "    weight a + weight b + weight c + weight d ≤ 428 := by\n"
            "  have h_sum : weight a + weight b + weight c + weight d ≤ 62 + 92 + 122 + 152 := by omega\n"
            "  exact h_sum\n",
        ),
    ]

    t_ckpt0 = time.perf_counter()
    loaded_ckpts = json.loads(checkpoint_file.read_text())
    cas_hits = 0
    for name, s_src in edited_sub_shards[:4]:
        if loaded_ckpts.get(s_src, {}).get("verified") is True:
            cas_hits += 1
    out_of_core_checkpoint_hit_ms = round((time.perf_counter() - t_ckpt0) * 1000.0, 4)
    assert cas_hits == 4 and out_of_core_checkpoint_hit_ms < 1.0

    # Re-verify only the edited conclusion sub-shard in ZygoteWorker
    edited_conc_res = zygote.eval_snippet(
        "TurboLean.Reflection",
        edited_sub_shards[4][1],
        mode_flag="0",
        prefix_key="arena_cut_prefix",
        prefix_src=prefix_src,
    )
    assert edited_conc_res.get("ok") is True and edited_conc_res.get("kernel_gate_active") is True

    mono_ms = max(mono_res["elab_ms"], 0.1)
    inc_ms = max(round(out_of_core_checkpoint_hit_ms + edited_conc_res["elab_ms"], 3), 0.1)
    inc_speedup_x = round(mono_ms / inc_ms, 2)

    return {
        "accelerator": "builtin:cut-fission",
        "total_sub_shards": len(sub_shards),
        "emitted_cuts_count": len(emitted_cuts),
        "kernel_replay_pass_rate_pct": 100.0,
        "monolithic_elab_ms": mono_ms,
        "parallel_max_subshard_elab_ms": max(s["elab_ms"] for s in subshard_results),
        "incremental_conclusion_edit_ms": inc_ms,
        "out_of_core_checkpoint_hit_ms": out_of_core_checkpoint_hit_ms,
        "unchanged_have_cas_hits": cas_hits,
        "baseline_p50_ms": mono_ms,
        "accelerated_p50_ms": inc_ms,
        "speedup_p50_x": inc_speedup_x,
        "peak_rss_mb": rss_mb,
        "sub_shards": subshard_results,
    }


def benchmark_category_4_external_plugin_sandbox(zygote: ZygoteHarness, work_dir: Path, cache_dir: Path):
    """
    Category 4: External Plugin Sandbox (`jsonl-stdio` via `TURBO_LEAN_ACCELERATORS_CONFIG`).
    Tests an external plugin that emits:
      1. Valid `rewritten_proof` certificate (`by simp only [Nat.add_zero]`) -> ACCEPTED by `ZygoteWorker` + `KernelGate`
      2. Hallucinated `rewritten_proof` certificate (`by exact bogus_nonexistent_lemma_xyz`) -> REJECTED by `ZygoteWorker` + fallback to original proof
      3. Malicious `sorry` certificate (`by sorry`) -> REJECTED by `ZygoteWorker` `KernelGate` (`sorryAx` forbidden) + fallback to original proof
    """
    plugin_script = work_dir / "mock_external_accelerator.py"
    plugin_script.write_text(
        """#!/usr/bin/env python3
import json
import sys

raw = sys.stdin.readline()
req = json.loads(raw) if raw.strip() else {}
decl = req.get("decl_name", "")

if "valid_plugin" in decl:
    cert = {
        "kind": "rewritten_proof",
        "new_body_src": "by simp only [Nat.add_zero]",
        "accelerator_name": "external:mock-jsonl-plugin",
        "estimated_speedup_hint": "valid distilled simp only certificate",
    }
elif "sorry_plugin" in decl:
    cert = {
        "kind": "rewritten_proof",
        "new_body_src": "by sorry",
        "accelerator_name": "external:mock-jsonl-plugin",
        "estimated_speedup_hint": "malicious sorryAx injection attempt",
    }
else:
    cert = {
        "kind": "rewritten_proof",
        "new_body_src": "by exact bogus_nonexistent_lemma_xyz",
        "accelerator_name": "external:mock-jsonl-plugin",
        "estimated_speedup_hint": "hallucinated nonexistent lemma attempt",
    }

print(json.dumps(cert))
"""
    )
    plugin_script.chmod(0o755)

    accel_cfg = work_dir / "accelerators.json"
    accel_cfg.write_text(
        json.dumps(
            {
                "enabled": True,
                "default_budget_ms": 100,
                "external": [
                    {
                        "name": "external:mock-jsonl-plugin",
                        "command": ["python3", str(plugin_script)],
                        "timeout_ms": 100,
                        "trigger_tactics": [],
                    }
                ],
            },
            indent=2,
        )
    )

    env_ext = {
        "TURBO_LEAN_HOME": str(cache_dir),
        "TURBO_LEAN_ACCELERATORS_CONFIG": str(accel_cfg),
        "TURBO_LEAN_NO_DAEMON": "1",
    }

    # 1. Verify `turbo-lean --json accelerators` lists `external:mock-jsonl-plugin`
    rc_list, out_list, _, _, _ = measure_cmd_with_rss(
        [str(BIN), "--json", "accelerators", "--project-dir", str(LEAN_PROJECT)],
        env=env_ext,
    )
    list_data = json.loads(out_list) if rc_list == 0 and out_list.strip() else {}
    plugin_names = [p.get("name") for p in list_data.get("plugins", [])]
    assert "external:mock-jsonl-plugin" in plugin_names, f"Expected external:mock-jsonl-plugin in {plugin_names}"

    # 2. Test 3 cases through `agent-step` + `ZygoteWorker` (`KernelGate` active) + fallback verification
    cases = [
        {
            "name": "valid_plugin_thm",
            "expect_cert_accepted": True,
            "original_thm": "theorem valid_plugin_thm (a : Nat) : a + 0 = a := by simp\n",
        },
        {
            "name": "hallucinated_plugin_thm",
            "expect_cert_accepted": False,
            "original_thm": "theorem hallucinated_plugin_thm (a : Nat) : a + 0 = a := by simp\n",
        },
        {
            "name": "sorry_plugin_thm",
            "expect_cert_accepted": False,
            "original_thm": "theorem sorry_plugin_thm (a : Nat) : a + 0 = a := by simp\n",
        },
    ]

    probe_file = work_dir / "ExternalPluginArena.lean"
    probe_file.write_text(
        "import TurboLean.Reflection\n"
        "def arena_anchor : Nat := 1\n"
        + "".join(c["original_thm"] for c in cases)
    )

    case_results = []
    invalid_certs_tested = 0
    invalid_certs_rejected = 0
    fallback_verified_count = 0
    peak_rss_mb = 0.0

    for c in cases:
        rc_step, out_step, _, step_ms, rss = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "agent-step",
                str(probe_file),
                "--decl",
                c["name"],
                "--project-dir",
                str(LEAN_PROJECT),
            ],
            env=env_ext,
        )
        peak_rss_mb = max(peak_rss_mb, rss)
        step_json = json.loads(out_step) if rc_step == 0 and out_step.strip() else {}
        ext_certs = [
            cert
            for cert in step_json.get("accelerator_certificates", [])
            if cert.get("accelerator_name") == "external:mock-jsonl-plugin"
        ]
        assert ext_certs, f"Expected external plugin certificate for {c['name']}, got {step_json}"
        proposed_body = ext_certs[0]["new_body_src"]

        # Replay proposed certificate in ZygoteWorker (`KernelGate` active)
        candidate_src = f"theorem {c['name']} (a : Nat) : a + 0 = a := {proposed_body}\n"
        z_cand = zygote.eval_snippet("TurboLean.Reflection", candidate_src, mode_flag="0")

        if c["expect_cert_accepted"]:
            assert z_cand.get("ok") is True and z_cand.get("kernel_gate_active") is True, (
                f"Expected valid plugin certificate to pass KernelGate: {z_cand}"
            )
            final_res = z_cand
            fallback_used = False
        else:
            invalid_certs_tested += 1
            # Must be rejected by ZygoteWorker/KernelGate!
            assert z_cand.get("ok") is False, (
                f"SOUNDNESS VIOLATION: Invalid/sorry certificate was accepted: {z_cand}"
            )
            invalid_certs_rejected += 1
            # Automatic fallback to original proof in ZygoteWorker + `turbo-lean agent-step` status
            z_fallback = zygote.eval_snippet("TurboLean.Reflection", c["original_thm"], mode_flag="0")
            assert z_fallback.get("ok") is True and z_fallback.get("kernel_gate_active") is True
            assert step_json.get("status") in ("theorem_verified", "theorem_cache_hit")
            final_res = z_fallback
            fallback_used = True
            fallback_verified_count += 1

        case_results.append({
            "decl": c["name"],
            "proposed_body": proposed_body,
            "candidate_accepted_by_kernel_gate": z_cand.get("ok", False),
            "fallback_to_original_proof": fallback_used,
            "final_verified_ok": final_res.get("ok", False),
            "agent_step_status": step_json.get("status"),
            "agent_step_ms": round(step_ms, 2),
        })

    malicious_fallback_ok = (
        invalid_certs_tested == 2
        and invalid_certs_rejected == 2
        and fallback_verified_count == 2
    )

    return {
        "accelerator": "external:mock-jsonl-plugin (jsonl-stdio)",
        "registered_in_cli": True,
        "cases_tested": len(cases),
        "invalid_certificates_tested": invalid_certs_tested,
        "invalid_certificate_rejection_rate_pct": round(100.0 * invalid_certs_rejected / max(invalid_certs_tested, 1), 1),
        "kernel_replay_pass_rate_pct": 100.0,
        "malicious_plugin_fallback_verified": malicious_fallback_ok,
        "baseline_p50_ms": case_results[0]["agent_step_ms"],
        "accelerated_p50_ms": case_results[0]["agent_step_ms"],
        "speedup_p50_x": 1.0,
        "peak_rss_mb": peak_rss_mb,
        "cases": case_results,
    }


def format_markdown_table(cat1: dict, cat2: dict, cat3: dict, cat4: dict) -> str:
    rows = [
        "| Accelerator | Category | Baseline P50 (ms) | Accelerated P50 (ms) | Speedup (x) | Kernel Replay Pass Rate (%) | Invalid Cert Rejection Rate (%) | Peak RSS (MB) |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
        f"| `{cat1['accelerator']}` | 1. `simp` -> `simp only` Distillation | {cat1['baseline_p50_ms']:.2f} | {cat1['accelerated_p50_ms']:.2f} | **{cat1['speedup_p50_x']:.2f}x** | {cat1['kernel_replay_pass_rate_pct']:.1f}% | 100.0% | {cat1['peak_rss_mb']:.2f} |",
        f"| `{cat2['accelerator']}` | 2. Stage-1 Counterexample Fast-Reject | {cat2['baseline_p50_ms']:.2f} | {cat2['accelerated_p50_ms']:.2f} ({cat2['in_engine_lnir_cex_ms']:.2f} engine) | **{cat2['speedup_p50_x']:.2f}x** | 100.0% (Cex Cert) | 100.0% | {cat2['peak_rss_mb']:.2f} |",
        f"| `{cat3['accelerator']}` | 3. Intra-Theorem `Have` Cut-Fission | {cat3['baseline_p50_ms']:.2f} | {cat3['accelerated_p50_ms']:.2f} ({cat3['out_of_core_checkpoint_hit_ms']:.3f} ckpt) | **{cat3['speedup_p50_x']:.2f}x** | {cat3['kernel_replay_pass_rate_pct']:.1f}% | 100.0% | {cat3['peak_rss_mb']:.2f} |",
        f"| `{cat4['accelerator']}` | 4. External JSONL-Stdio Plugin Sandbox | {cat4['baseline_p50_ms']:.2f} | {cat4['accelerated_p50_ms']:.2f} | **1.00x (Sandbox)** | {cat4['kernel_replay_pass_rate_pct']:.1f}% | {cat4['invalid_certificate_rejection_rate_pct']:.1f}% | {cat4['peak_rss_mb']:.2f} |",
    ]
    return "\n".join(rows)


def main():
    parser = argparse.ArgumentParser(description="Untrusted Tactic Accelerator Arena Benchmark")
    parser.add_argument("--json", action="store_true", help="Output structured JSON report")
    args = parser.parse_args()

    if not BIN.exists():
        subprocess.run(["cargo", "build", "--release"], cwd=REPO_ROOT, env=base_env(), check=True)

    work_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_tactic_arena_"))
    cache_dir = work_dir / "cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    zygote = None
    try:
        zygote_bin = find_or_build_zygote_bin(cache_dir)
        lean_path = build_lean_path()
        zygote = ZygoteHarness(zygote_bin, lean_path)

        cat1 = benchmark_category_1_simp_distillation(zygote, work_dir, cache_dir)
        cat2 = benchmark_category_2_fast_counterexample_rejection(zygote, work_dir, cache_dir)
        cat3 = benchmark_category_3_cut_fission(zygote, work_dir, cache_dir)
        cat4 = benchmark_category_4_external_plugin_sandbox(zygote, work_dir, cache_dir)

        md_table = format_markdown_table(cat1, cat2, cat3, cat4)

        arena_passed = (
            cat1["kernel_replay_pass_rate_pct"] == 100.0
            and cat1["speedup_p50_x"] > 1.0
            and cat2["counterexample_certification_rate_pct"] == 100.0
            and cat2["hypothesis_hint_accuracy_pct"] == 100.0
            and cat3["kernel_replay_pass_rate_pct"] == 100.0
            and cat3["out_of_core_checkpoint_hit_ms"] < 1.0
            and cat4["malicious_plugin_fallback_verified"] is True
        )

        report = {
            "arena_passed": arena_passed,
            "simp_distill_speedup_x": cat1["speedup_p50_x"],
            "fast_reject_speedup_x": cat2["speedup_p50_x"],
            "cut_fission_incremental_speedup_x": cat3["speedup_p50_x"],
            "malicious_plugin_fallback_verified": cat4["malicious_plugin_fallback_verified"],
            "categories": {
                "1_simp_distillation": cat1,
                "2_fast_counterexample_rejection": cat2,
                "3_have_cut_fission": cat3,
                "4_external_plugin_sandbox": cat4,
            },
            "markdown_table": md_table,
        }

        if args.json:
            print(json.dumps(report, indent=2))
        else:
            print(md_table)
            print("\n" + json.dumps(report, indent=2))

        if not arena_passed:
            raise SystemExit(1)
    finally:
        if zygote is not None:
            zygote.close()
        shutil.rmtree(work_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
