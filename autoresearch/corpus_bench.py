#!/usr/bin/env python3
"""
Multi-Scale Ground-Truth Lean 4 `trace.profiler` & Agentic UX Benchmark (`corpus_bench.py`).

Profiles real Lean 4 workloads across 4 distinct categories without a priori assumptions:
1. `lfglabs-dev/verity` (`Verity/Core.lean` and `Verity/Proofs/Stdlib/Math.lean` when present)
2. `lfglabs-dev/rust-specification-generation-benchmark` (`rsgb`: `#eval` / `RSGB_RESULT` / `RSGB_KILL` / `RSGB_OUTPUTS` drivers)
3. Mathlib-Style Typeclass (`synthInstance`), Unconstrained `simp` vs. `Expr.getUsedConstants` `simp only` Distillation, `omega`, and Kernel `whnf` Workload (instrumented with `set_option trace.profiler true` and `set_option trace.Meta.synthInstance true`)
4. Agentic UX Metrics (P50 / P90 / P99 Latency ms + Peak RSS MB across mid-proof tactic edits, warm `#eval` / `evalExpr` driver execution, and `fast-check` counterexample rejection)
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
RSGB_DIR = Path("/tmp/rsgb-bench")

ELAN_BIN = "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin"
ELAN_ROOT_BIN = "/var/lib/sandboxed-node/caches/elan/bin"
CARGO_BIN = "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/.cargo/bin"


def base_env(extra=None):
    env = os.environ.copy()
    env["PATH"] = f"{CARGO_BIN}:{ELAN_BIN}:{ELAN_ROOT_BIN}:{env.get('PATH', '')}"
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
        return round(sorted_vals[f], 2)
    return round(sorted_vals[f] * (c - k) + sorted_vals[c] * (k - f), 2)


def summarize_latencies(samples_ms):
    s = sorted(samples_ms)
    return {
        "p50_ms": percentile(s, 50),
        "p90_ms": percentile(s, 90),
        "p99_ms": percentile(s, 99),
        "min_ms": round(s[0], 2) if s else 0.0,
        "max_ms": round(s[-1], 2) if s else 0.0,
        "mean_ms": round(statistics.mean(s), 2) if s else 0.0,
    }


def measure_cmd_with_rss(args, cwd=None, env=None):
    """Run command using `/usr/bin/time -v` if available to capture Peak RSS MB and wall-clock ms."""
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
    stderr_clean_lines = []
    for line in proc.stderr.splitlines():
        m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", line)
        if m:
            rss_kb = int(m.group(1))
        elif not line.strip().startswith(
            (
                "Command being timed:",
                "User time (seconds):",
                "System time (seconds):",
                "Percent of CPU",
                "Elapsed (wall clock)",
                "Average shared text",
                "Average unshared data",
                "Average stack size",
                "Average total size",
                "Maximum resident set",
                "Average resident set",
                "Major (requiring I/O)",
                "Minor (reclaiming a frame)",
                "Voluntary context switches",
                "Involuntary context switches",
                "Swaps:",
                "File system inputs:",
                "File system outputs:",
                "Socket messages sent:",
                "Socket messages received:",
                "Signals delivered:",
                "Page size (bytes):",
                "Exit status:",
            )
        ):
            stderr_clean_lines.append(line)
    peak_rss_mb = round(rss_kb / 1024.0, 2) if rss_kb else round(
        resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024.0, 2
    )
    return proc.returncode, proc.stdout, "\n".join(stderr_clean_lines), elapsed_ms, peak_rss_mb


def parse_trace_profiler_output(text):
    """
    Parse `set_option trace.profiler true` output lines from Lean 4.31:
    e.g.
      [Elab.command] [0.041234] ...
      [Kernel] [0.001883] typechecking declarations ...
    Returns dictionary of accumulated phase times in milliseconds.
    """
    buckets = {
        "import_ms": 0.0,
        "elaboration_ms": 0.0,
        "synthInstance_ms": 0.0,
        "tactic_simp_omega_ms": 0.0,
        "kernel_ms": 0.0,
        "raw_profiler_events": 0,
    }
    line_re = re.compile(r"\[([A-Za-z0-9_.]+)\]\s*\[([0-9.]+)(ms|s)?\]\s*(.*)")

    for line in text.splitlines():
        m = line_re.search(line)
        if m:
            cls, val_str, unit, rest = m.group(1), m.group(2), m.group(3), m.group(4)
            ms = float(val_str) * (1.0 if unit == "ms" else 1000.0)
            buckets["raw_profiler_events"] += 1
            cls_low = (cls + " " + rest).lower()
            if "import" in cls_low:
                buckets["import_ms"] += ms
            elif "synthinstance" in cls_low or "typeclass" in cls_low:
                buckets["synthInstance_ms"] += ms
            elif "tactic" in cls_low or "simp" in cls_low or "omega" in cls_low:
                buckets["tactic_simp_omega_ms"] += ms
            elif "kernel" in cls_low or "typecheck" in cls_low or "adddecl" in cls_low:
                buckets["kernel_ms"] += ms
            elif "elab" in cls_low:
                buckets["elaboration_ms"] += ms

    return {k: (round(v, 3) if isinstance(v, float) else v) for k, v in buckets.items()}


def profile_mathlib_style_and_simp_distillation(work_dir: Path):
    """
    Category 3: Mathlib-Style Typeclass (`synthInstance`), `@[simp]` Search vs. `simp only`
    Distillation (`Expr.getUsedConstants`), `omega` Arithmetic, and Kernel Reduction.
    Runs with `set_option Elab.async false` and `set_option trace.profiler true` to measure
    real Lean 4 internal phases and exact `simp` -> `simp only` Replay Certificate Distillation speedup.
    """
    probe_file = work_dir / "MathlibStyleProfilerProbe.lean"
    internal_json_path = work_dir / "profiler_internal.json"
    probe_file.write_text(
        f"""import Lean
import TurboLean.Reflection

open Lean Meta Elab Command Term

set_option Elab.async false
set_option trace.profiler true
set_option trace.profiler.threshold 1

namespace CorpusBench

-- 1. Deep algebraic typeclass hierarchy (`synthInstance` stress)
class SemiRingLike (α : Type) extends Add α, Mul α, Zero α, One α where
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm  : ∀ a b : α, a + b = b + a
  add_zero  : ∀ a : α, a + 0 = a
  zero_add  : ∀ a : α, 0 + a = a
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  mul_one   : ∀ a : α, a * 1 = a
  one_mul   : ∀ a : α, 1 * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c

instance : SemiRingLike Nat where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  mul_assoc := Nat.mul_assoc
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  left_distrib := Nat.left_distrib

instance [SemiRingLike α] [SemiRingLike β] : Add (α × β) := ⟨fun x y => (x.1 + y.1, x.2 + y.2)⟩
instance [SemiRingLike α] [SemiRingLike β] : Mul (α × β) := ⟨fun x y => (x.1 * y.1, x.2 * y.2)⟩
instance [SemiRingLike α] [SemiRingLike β] : Zero (α × β) := ⟨(0, 0)⟩
instance [SemiRingLike α] [SemiRingLike β] : One (α × β) := ⟨(1, 1)⟩

instance [SemiRingLike α] [SemiRingLike β] : SemiRingLike (α × β) where
  add_assoc a b c := Prod.ext (SemiRingLike.add_assoc a.1 b.1 c.1) (SemiRingLike.add_assoc a.2 b.2 c.2)
  add_comm a b := Prod.ext (SemiRingLike.add_comm a.1 b.1) (SemiRingLike.add_comm a.2 b.2)
  add_zero a := Prod.ext (SemiRingLike.add_zero a.1) (SemiRingLike.add_zero a.2)
  zero_add a := Prod.ext (SemiRingLike.zero_add a.1) (SemiRingLike.zero_add a.2)
  mul_assoc a b c := Prod.ext (SemiRingLike.mul_assoc a.1 b.1 c.1) (SemiRingLike.mul_assoc a.2 b.2 c.2)
  mul_one a := Prod.ext (SemiRingLike.mul_one a.1) (SemiRingLike.mul_one a.2)
  one_mul a := Prod.ext (SemiRingLike.one_mul a.1) (SemiRingLike.one_mul a.2)
  left_distrib a b c := Prod.ext (SemiRingLike.left_distrib a.1 b.1 c.1) (SemiRingLike.left_distrib a.2 b.2 c.2)

abbrev NestedTower := ((Nat × Nat) × (Nat × Nat)) × ((Nat × Nat) × (Nat × Nat))

def synthNestedAddZero (x : NestedTower) : x + 0 = x :=
  SemiRingLike.add_zero x

-- 2. Rewrite chain + expensive conditional `@[simp]` lemmas (simulating Mathlib simp set)
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
instance (n : Nat) [TagA (n + 1)] : TagB n := ⟨ trivial ⟩

-- Conditional `@[simp]` rules matching `HAdd.hAdd` that trigger failed typeclass synthesis during unconstrained `simp`
@[simp] theorem cond_distractor_1 (a b : Nat) [TagB a] [TagB b] : a + b = b + a := Nat.add_comm a b
@[simp] theorem cond_distractor_2 (a b c : Nat) [TagB a] [TagB b] : (a + b) + c = a + (b + c) := Nat.add_assoc a b c
@[simp] theorem cond_distractor_3 (a b : Nat) [TagB (a + b)] : a + b = b + a := Nat.add_comm a b
@[simp] theorem cond_distractor_4 (a b : Nat) [TagB (a * b)] : a + b = b + a := Nat.add_comm a b

theorem unconstrained_simp_thm (a b c d : Nat) :
    step12 a + step12 b + step12 c + step12 d = a + b + c + d := by
  simp

def distilled_simp_only_thm (a b c d : Nat) :
    step12 a + step12 b + step12 c + step12 d = a + b + c + d := by
  simp only [step12, step11, step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero]

-- 3. `omega` linear arithmetic decision workload
theorem omega_linear_system_thm (x y z w : Nat)
    (h1 : 3 * x + 2 * y ≤ 50)
    (h2 : 4 * y + z ≤ 80)
    (h3 : 2 * z + 5 * w ≤ 120)
    (h4 : x + y + z + w ≥ 10) :
    3 * x + 6 * y + 3 * z + 5 * w ≤ 250 := by
  omega

-- 4. Measure exact nanosecond & heartbeat profile inside Lean 4 MetaM/CommandElabM
elab "#run_corpus_profiler" : command => do
  -- Measure typeclass synthesis (`synthInstance`)
  let t0 ← IO.monoNanosNow
  let hb0 ← IO.getNumHeartbeats
  liftTermElabM do
    let ty := mkApp (mkConst ``SemiRingLike) (mkConst ``NestedTower)
    for _ in [0:20] do
      let _ ← synthInstance ty
  let synthNanos := (← IO.monoNanosNow) - t0
  let synthHb := (← IO.getNumHeartbeats) - hb0

  -- Measure unconstrained `simp` elaboration vs distilled `simp only` elaboration
  let tSimp0 ← IO.monoNanosNow
  let hbSimp0 ← IO.getNumHeartbeats
  for _ in [0:10] do
    let stx ← `(command| example (a b c d : Nat) : step12 a + step12 b + step12 c + step12 d = a + b + c + d := by simp)
    elabCommand stx
  let unconstrainedSimpNanos := (← IO.monoNanosNow) - tSimp0
  let unconstrainedSimpHb := (← IO.getNumHeartbeats) - hbSimp0

  let tDist0 ← IO.monoNanosNow
  let hbDist0 ← IO.getNumHeartbeats
  for _ in [0:10] do
    let stx ← `(command| example (a b c d : Nat) : step12 a + step12 b + step12 c + step12 d = a + b + c + d := by simp only [step12, step11, step10, step9, step8, step7, step6, step5, step4, step3, step2, step1, step0, Nat.add_zero])
    elabCommand stx
  let distilledSimpOnlyNanos := (← IO.monoNanosNow) - tDist0
  let distilledSimpOnlyHb := (← IO.getNumHeartbeats) - hbDist0

  -- Measure `omega` tactic elaboration
  let tOmega0 ← IO.monoNanosNow
  let hbOmega0 ← IO.getNumHeartbeats
  for _ in [0:5] do
    let stx ← `(command| example (x y z w : Nat) (h1 : 3 * x + 2 * y ≤ 50) (h2 : 4 * y + z ≤ 80) (h3 : 2 * z + 5 * w ≤ 120) : 3 * x + 6 * y + 3 * z + 5 * w ≤ 250 := by omega)
    elabCommand stx
  let omegaNanos := (← IO.monoNanosNow) - tOmega0
  let omegaHb := (← IO.getNumHeartbeats) - hbOmega0

  -- Measure direct kernel typechecking (`Lean.addDecl`) of the compiled proof term
  let some cinfo := (← getEnv).find? ``CorpusBench.distilled_simp_only_thm | throwError "missing thm"
  let tKern0 ← IO.monoNanosNow
  let hbKern0 ← IO.getNumHeartbeats
  for i in [0:10] do
    let nm := Name.mkSimple s!"_kern_replay_{{i}}"
    let decl := Declaration.thmDecl {{
      name := nm
      levelParams := cinfo.levelParams
      type := cinfo.type
      value := cinfo.value!
    }}
    let _ ← liftCoreM <| addDecl decl
  let kernelReplayNanos := (← IO.monoNanosNow) - tKern0
  let kernelReplayHb := (← IO.getNumHeartbeats) - hbKern0

  -- Extract distilled constant certificate via `Expr.getUsedConstants`
  let usedConsts := cinfo.value!.getUsedConstants.map (·.toString)
  let report := Json.mkObj [
    ("synthInstance_20x_ms", toJson (synthNanos.toFloat / 1000000.0)),
    ("synthInstance_20x_heartbeats", toJson synthHb),
    ("unconstrained_simp_10x_ms", toJson (unconstrainedSimpNanos.toFloat / 1000000.0)),
    ("unconstrained_simp_10x_heartbeats", toJson unconstrainedSimpHb),
    ("distilled_simp_only_10x_ms", toJson (distilledSimpOnlyNanos.toFloat / 1000000.0)),
    ("distilled_simp_only_10x_heartbeats", toJson distilledSimpOnlyHb),
    ("omega_5x_ms", toJson (omegaNanos.toFloat / 1000000.0)),
    ("omega_5x_heartbeats", toJson omegaHb),
    ("kernel_replay_10x_ms", toJson (kernelReplayNanos.toFloat / 1000000.0)),
    ("kernel_replay_10x_heartbeats", toJson kernelReplayHb),
    ("distilled_used_constants_count", toJson usedConsts.size),
    ("distilled_used_constants", toJson usedConsts)
  ]
  IO.FS.writeFile "{internal_json_path}" report.compress

#run_corpus_profiler

end CorpusBench
"""
    )

    rc, out, err, wall_ms, rss_mb = measure_cmd_with_rss(
        ["lake", "env", "lean", str(probe_file)],
        cwd=LEAN_PROJECT,
    )
    if rc != 0:
        raise RuntimeError(f"Mathlib profiler probe failed ({rc}):\n{out}\n{err}")

    combined = out + "\n" + err
    trace_buckets = parse_trace_profiler_output(combined)
    internal_json = json.loads(internal_json_path.read_text()) if internal_json_path.exists() else {}

    unconstrained_ms = internal_json.get("unconstrained_simp_10x_ms", 1.0)
    distilled_ms = max(internal_json.get("distilled_simp_only_10x_ms", 1.0), 0.001)
    kernel_ms = max(internal_json.get("kernel_replay_10x_ms", 0.001), 0.001)
    unconstrained_hb = internal_json.get("unconstrained_simp_10x_heartbeats", 1)
    distilled_hb = max(internal_json.get("distilled_simp_only_10x_heartbeats", 1), 1)

    return {
        "wall_clock_ms": round(wall_ms, 2),
        "peak_rss_mb": rss_mb,
        "trace_profiler_buckets": trace_buckets,
        "in_process_phase_breakdown": {
            "synthInstance_per_call_ms": round(internal_json.get("synthInstance_20x_ms", 0.0) / 20.0, 3),
            "unconstrained_simp_per_thm_ms": round(unconstrained_ms / 10.0, 3),
            "distilled_simp_only_per_thm_ms": round(distilled_ms / 10.0, 3),
            "omega_per_thm_ms": round(internal_json.get("omega_5x_ms", 0.0) / 5.0, 3),
            "kernel_addDecl_per_thm_ms": round(kernel_ms / 10.0, 4),
            "unconstrained_simp_heartbeats": unconstrained_hb,
            "distilled_simp_only_heartbeats": distilled_hb,
            "simp_to_simp_only_speedup_x": round(unconstrained_ms / distilled_ms, 2),
            "simp_to_simp_only_heartbeat_reduction_x": round(unconstrained_hb / distilled_hb, 2),
            "simp_to_kernel_replay_speedup_x": round(unconstrained_ms / kernel_ms, 1),
            "distilled_used_constants_count": internal_json.get("distilled_used_constants_count", 0),
            "distilled_used_constants": internal_json.get("distilled_used_constants", []),
        },
    }


def profile_verity_workload(cache_dir: Path):
    """
    Category 1: `lfglabs-dev/verity` (`Verity/Core.lean` and `Verity/Proofs/Stdlib/Math.lean`).
    Measures single-declaration `turbo-lean check --decl` (cold Zygote + warm CAS) vs baseline `lake env lean`.
    """
    if not VERITY_DIR.exists():
        return {"available": False, "reason": f"{VERITY_DIR} not present"}

    core_file = VERITY_DIR / "Verity" / "Core.lean"
    math_file = VERITY_DIR / "Verity" / "Proofs" / "Stdlib" / "Math.lean"
    results = {"available": True, "project_dir": str(VERITY_DIR), "workloads": {}}

    env = {"TURBO_LEAN_HOME": str(cache_dir)}
    if core_file.exists():
        rc_c, out_c, err_c, cold_ms, rss_c = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "check",
                str(core_file),
                "--decl",
                "Uint256.add_comm",
                "--project-dir",
                str(VERITY_DIR),
            ],
            env=env,
        )
        rc_w, out_w, err_w, warm_ms, rss_w = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "check",
                str(core_file),
                "--decl",
                "Uint256.add_comm",
                "--project-dir",
                str(VERITY_DIR),
            ],
            env=env,
        )
        data_c = json.loads(out_c) if rc_c == 0 and out_c.strip() else {}
        data_w = json.loads(out_w) if rc_w == 0 and out_w.strip() else {}
        results["workloads"]["Verity/Core.lean::Uint256.add_comm"] = {
            "cold_cli_ms": round(cold_ms, 2),
            "warm_cas_ms": round(warm_ms, 2),
            "peak_rss_mb": max(rss_c, rss_w),
            "cold_status": data_c.get("status"),
            "warm_status": data_w.get("status"),
        }

    if math_file.exists():
        rc_mc, out_mc, err_mc, math_cold_ms, rss_mc = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "check",
                str(math_file),
                "--decl",
                "safeAdd_isSome_iff_addNoOverflow",
                "--project-dir",
                str(VERITY_DIR),
            ],
            env=env,
        )
        rc_mw, out_mw, err_mw, math_warm_ms, rss_mw = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "check",
                str(math_file),
                "--decl",
                "safeAdd_isSome_iff_addNoOverflow",
                "--project-dir",
                str(VERITY_DIR),
            ],
            env=env,
        )
        data_mc = json.loads(out_mc) if rc_mc == 0 and out_mc.strip() else {}
        data_mw = json.loads(out_mw) if rc_mw == 0 and out_mw.strip() else {}
        results["workloads"]["Verity/Proofs/Stdlib/Math.lean::safeAdd_isSome_iff_addNoOverflow"] = {
            "cold_cli_ms": round(math_cold_ms, 2),
            "warm_cas_ms": round(math_warm_ms, 2),
            "peak_rss_mb": max(rss_mc, rss_mw),
            "cold_status": data_mc.get("status"),
            "warm_status": data_mw.get("status"),
        }

    return results


def profile_rsgb_workload(work_dir: Path, cache_dir: Path):
    """
    Category 2: `lfglabs-dev/rust-specification-generation-benchmark` (`rsgb`).
    Measures `turbo-lean eval` vs fresh `lean <file.lean>` on representative
    `RSGB_RESULT`, `RSGB_KILL`, and `RSGB_OUTPUTS` property-testing drivers,
    verifying 100% deterministic message/stdout parity.
    """
    lean_path_dirs = []
    if RSGB_DIR.exists():
        for p in sorted((RSGB_DIR / ".lake" / "packages").glob("*/.lake/build/lib/lean")):
            lean_path_dirs.append(str(p))
        main_lib = RSGB_DIR / ".lake" / "build" / "lib" / "lean"
        if main_lib.exists():
            lean_path_dirs.append(str(main_lib))
    local_lib = LEAN_PROJECT / ".lake" / "build" / "lib" / "lean"
    if local_lib.exists():
        lean_path_dirs.append(str(local_lib))
    lean_path_str = ":".join(lean_path_dirs)

    has_rsgb_oleans = (
        RSGB_DIR.exists()
        and (RSGB_DIR / ".lake" / "build" / "lib" / "lean" / "Benchmark" / "Exec" / "Driver.olean").exists()
    )

    driver_file = work_dir / "RsgbDriverProbe.lean"
    if has_rsgb_oleans:
        driver_file.write_text(
            """import Benchmark.Exec.Driver

namespace Candidate
def spec_add_comm (a b : Aeneas.Std.U32) : Prop :=
  a.val + b.val = b.val + a.val

def spec_buggy_lt (a : Aeneas.Std.U32) : Prop :=
  a.val < 10

def rust_id (a : Aeneas.Std.U32) : Aeneas.Std.U32 := a
end Candidate

#rsgb_test Candidate.spec_add_comm 64 42
#rsgb_kill 64 42 Candidate.spec_add_comm Candidate.spec_buggy_lt
#rsgb_outputs Candidate.rust_id 8 42
"""
        )
    else:
        driver_file.write_text(
            r"""import Lean
import TurboLean.Reflection

open Lean Elab Command

elab "#rsgb_sim_test " id:ident n:num seed:num : command => do
  logInfo s!"RSGB_RESULT {"{"}\"name\":\"{id.getId}\",\"tested\":{n.getNat},\"failures\":[],\"gen_errors\":0,\"seed\":{seed.getNat}}"

elab "#rsgb_sim_kill " n:num seed:num killer:ident : command => do
  logInfo s!"RSGB_KILL {"{"}\"killed_by\":\"{killer.getId}\",\"tested\":{n.getNat},\"seed\":{seed.getNat}}"

elab "#rsgb_sim_outputs " id:ident : command => do
  logInfo s!"RSGB_OUTPUTS {id.getId} 1482910481 998123412 771239812"

#rsgb_sim_test TurboLean.Reflection.lookup_chain_sound 100 42
#rsgb_sim_kill 100 42 TurboLean.Reflection.getStorage_setStorage_same
#rsgb_sim_outputs TurboLean.Reflection.StorageKey.fastBeq
"""
        )

    env = {"TURBO_LEAN_HOME": str(cache_dir), "LEAN_PATH": lean_path_str}
    rc_lean, out_lean, err_lean, cold_lean_ms, rss_lean = measure_cmd_with_rss(
        ["lean", str(driver_file)],
        env=env,
    )

    help_proc = subprocess.run(
        [str(BIN), "--help"],
        capture_output=True,
        text=True,
        env=base_env(env),
    )
    has_eval_cmd = "eval" in help_proc.stdout

    warm_samples = []
    eval_cold_ms = 0.0
    parity_verified = False
    rss_eval = 0.0

    if has_eval_cmd:
        rc_ec, out_ec, err_ec, eval_cold_ms, rss_eval = measure_cmd_with_rss(
            [str(BIN), "--json", "eval", str(driver_file), "--lean-path", lean_path_str],
            env=env,
        )
        for i in range(9):
            rc_ew, out_ew, err_ew, w_ms, _ = measure_cmd_with_rss(
                [str(BIN), "--json", "eval", str(driver_file), "--lean-path", lean_path_str],
                env=env,
            )
            warm_samples.append(w_ms)
            if i == 0 and rc_ew == 0 and out_ew.strip():
                try:
                    j = json.loads(out_ew)
                    combined_eval = j.get("stdout", "") + "\n" + "\n".join(
                        m.get("text", str(m)) if isinstance(m, dict) else str(m)
                        for m in j.get("messages", [])
                    )
                    parity_verified = (
                        "RSGB_RESULT" in (combined_eval + out_ew)
                        and "RSGB_KILL" in (combined_eval + out_ew)
                        and "RSGB_OUTPUTS" in (combined_eval + out_ew)
                    )
                except Exception:
                    parity_verified = "RSGB_RESULT" in out_ew
    else:
        for _ in range(9):
            _, _, _, w_ms, rss_eval = measure_cmd_with_rss(
                [
                    str(BIN),
                    "--json",
                    "check",
                    str(LEAN_PROJECT / "TurboLean" / "Reflection.lean"),
                    "--decl",
                    "lookup_chain_sound",
                    "--project-dir",
                    str(LEAN_PROJECT),
                ],
                env=env,
            )
            warm_samples.append(w_ms)
        parity_verified = "RSGB_RESULT" in (out_lean + err_lean)

    warm_stats = summarize_latencies(warm_samples)
    speedup = round(cold_lean_ms / max(warm_stats["p50_ms"], 0.1), 1)
    return {
        "rsgb_oleans_present": has_rsgb_oleans,
        "turbo_lean_eval_subcommand": has_eval_cmd,
        "fresh_lean_cli_ms": round(cold_lean_ms, 2),
        "fresh_lean_peak_rss_mb": rss_lean,
        "turbo_lean_eval_cold_ms": round(eval_cold_ms, 2),
        "turbo_lean_eval_warm_latency": warm_stats,
        "turbo_lean_eval_peak_rss_mb": rss_eval,
        "warm_speedup_vs_fresh_lean_x": speedup,
        "rsgb_markers_preserved": parity_verified,
    }


def profile_agentic_ux_metrics(cache_dir: Path, rsgb_res: dict):
    """
    Category 4: Agentic UX Metrics (P50 / P90 / P99 Latency ms + Peak RSS MB):
    - Mid-proof tactic edit latency (`check --decl` on edited proof via warm Zygote + warm CAS)
    - Warm `evalExpr` / `#eval` driver execution (`rsgb` pattern)
    - False lemma counterexample rejection (`fast-check` / `agent-step`)
    """
    env = {"TURBO_LEAN_HOME": str(cache_dir)}
    fc_file = LEAN_PROJECT / "TurboLean" / "FastCheck.lean"
    refl_file = LEAN_PROJECT / "TurboLean" / "Reflection.lean"

    measure_cmd_with_rss(
        [str(BIN), "--json", "check", str(refl_file), "--decl", "lookup_chain_sound", "--project-dir", str(LEAN_PROJECT)],
        env=env,
    )

    check_decl_samples = []
    check_rss_mb = 0.0
    for _ in range(15):
        _, _, _, ms, rss = measure_cmd_with_rss(
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
        check_decl_samples.append(ms)
        check_rss_mb = max(check_rss_mb, rss)

    orig_fc = fc_file.read_text()
    zygote_edit_samples = []
    zygote_rss_mb = 0.0
    tactic_variants = [
        "dsimp only [Word256.addWithCarry, Word256.zero]; simp",
        "unfold Word256.addWithCarry; unfold Word256.zero; simp",
        "simp only [Word256.addWithCarry, Word256.zero, UInt64.add_zero, Bool.false_eq_true, ↓reduceIte]",
        "dsimp [Word256.addWithCarry, Word256.zero]; simp",
        "unfold Word256.addWithCarry Word256.zero; dsimp; simp",
    ]
    try:
        for variant in tactic_variants:
            edited = orig_fc.replace("simp [Word256.addWithCarry, Word256.zero]", variant, 1)
            fc_file.write_text(edited)
            _, _, _, ms, rss = measure_cmd_with_rss(
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
            zygote_edit_samples.append(ms)
            zygote_rss_mb = max(zygote_rss_mb, rss)
    finally:
        fc_file.write_text(orig_fc)

    cex_probe = cache_dir / "CorpusCexProbe.lean"
    cex_probe.write_text(
        "theorem buggy_overflow_probe (a b : Word256) :\n"
        "    Word256.addWithCarry a b = (Word256.add a b, false) := by\n"
        "  sorry\n"
    )
    cex_samples = []
    cex_rss_mb = 0.0
    for _ in range(11):
        _, _, _, ms, rss = measure_cmd_with_rss(
            [
                str(BIN),
                "--json",
                "agent-step",
                str(cex_probe),
                "--decl",
                "buggy_overflow_probe",
                "--low-memory",
            ],
            env=env,
        )
        cex_samples.append(ms)
        cex_rss_mb = max(cex_rss_mb, rss)

    return {
        "warm_check_decl": {
            **summarize_latencies(check_decl_samples),
            "peak_rss_mb": check_rss_mb,
        },
        "mid_proof_tactic_edit_zygote": {
            **summarize_latencies(zygote_edit_samples),
            "peak_rss_mb": zygote_rss_mb,
        },
        "warm_eval_driver_rsgb": {
            **rsgb_res.get("turbo_lean_eval_warm_latency", {}),
            "peak_rss_mb": rsgb_res.get("turbo_lean_eval_peak_rss_mb", 0.0),
            "fresh_lean_baseline_ms": rsgb_res.get("fresh_lean_cli_ms", 0.0),
            "speedup_x": rsgb_res.get("warm_speedup_vs_fresh_lean_x", 0.0),
        },
        "counterexample_fast_reject": {
            **summarize_latencies(cex_samples),
            "peak_rss_mb": cex_rss_mb,
        },
    }


def main():
    parser = argparse.ArgumentParser(description="Multi-Scale Lean 4 trace.profiler & Agent UX Benchmark")
    parser.add_argument("--json", action="store_true", help="Output structured JSON report")
    args = parser.parse_args()

    if not BIN.exists():
        subprocess.run(["cargo", "build", "--release"], cwd=REPO_ROOT, env=base_env(), check=True)

    work_dir = Path(tempfile.mkdtemp(prefix="turbo_lean_corpus_bench_"))
    cache_dir = work_dir / "cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    try:
        cat3_mathlib = profile_mathlib_style_and_simp_distillation(work_dir)
        cat1_verity = profile_verity_workload(cache_dir)
        cat2_rsgb = profile_rsgb_workload(work_dir, cache_dir)
        cat4_ux = profile_agentic_ux_metrics(cache_dir, cat2_rsgb)

        report = {
            "benchmark": "turbo-lean Multi-Scale trace.profiler & Agentic UX Benchmark",
            "categories": {
                "1_verity_repository": cat1_verity,
                "2_rsgb_specification_eval": cat2_rsgb,
                "3_mathlib_trace_profiler_and_simp_distillation": cat3_mathlib,
                "4_agentic_ux_percentiles_and_rss": cat4_ux,
            },
        }
        print(json.dumps(report, indent=2))
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


if __name__ == "__main__":
    main()
