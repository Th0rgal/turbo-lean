#!/usr/bin/env python3
"""Scalar-only differential conformance probe, not full Tier C4 acceptance.

Executes THREE genuinely independent engines on EVERY seed and corpus program:
  1. Engine 1 (`stock_lean_c`): Elaborates & compiles the generated `.lean` source file with
     the stock Lean 4 compiler (`lean -c` + `leanc`) and its unmodified runtime.
  2. Engine 2 (`lnir_eval`): Lowers the same `.lean` program to `LNIR` via the real compiler
     frontend (`lean-native emit-lnir --wire <FuzzerBatch.lean>`) and evaluates EVERY declaration
     with the formal operational interpreter (`lean-native-core eval-lnir --batch-json --opt`),
     plus the repository's symbolic translation validator (`lean-native-core validate-tv`).
  3. Engine 3 (`leannative_llvm_binary`): Compiles the lowered `LNIRModule` through `LeanNative`'s
     LLVM backend (`lean-native-core compile-llvm`) and `clang` into a native executable and runs it.

Hard Fail-Closed Contract (`P0`/`P1`):
  - If ANY required engine (`lean`, `lean-native`, `lean-native-core`, `clang`) is missing or not
    executable, `run_fuzzer` returns `ok: False, status: "incomplete_missing_engine"` and exits non-zero.
  - Precomputed `program["value"]` or Python-only fallback is NEVER used as an engine output.
   - Alias-shaped cases are scalar conditionals; loop-shaped cases are unrolled additions.
     Neither exercises aliasing, RC, or LNIR seqFor. No RC coverage is claimed.
   - Every batch execution records SHA-256 digests of the `.lean` source, frontend-lowered `.lnir`,
    emitted `.ll`, and compiled binaries in the receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LEAN_NATIVE_CORE = ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native-core"
LEAN_NATIVE_FULL = ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native"
MASK64 = (1 << 64) - 1

BOUNDARY_SCALARS: tuple[int, ...] = (
    0,
    1,
    2,
    31,
    32,
    63,
    64,
    (1 << 31) - 1,
    1 << 31,
    (1 << 63) - 1,
    1 << 63,
    (1 << 64) - 1,
)
LOOP_STEPS: tuple[int, ...] = (0, 1, 2, 7)
OPS = ("add", "sub", "mul", "shl", "shr", "and", "xor")


def u64(n: int) -> int:
    return n & MASK64


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def splitmix64(seed: int) -> int:
    z = u64(seed + 0x9E3779B97F4A7C15)
    z = u64((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9)
    z = u64((z ^ (z >> 27)) * 0x94D049BB133111EB)
    return z ^ (z >> 31)


class Rng:
    """Deterministic xorshift64* so a seed replays bit-for-bit."""

    def __init__(self, seed: int) -> None:
        self.state = seed & MASK64 or 0xA5A5A5A5A5A5A5A5

    def next_u64(self) -> int:
        x = self.state
        x ^= (x >> 12) & MASK64
        x ^= (x << 25) & MASK64
        x ^= (x >> 27) & MASK64
        self.state = x & MASK64
        return u64(x * 0x2545F4914F6CDD1D)

    def choice(self, n: int) -> int:
        return self.next_u64() % n if n else 0


def pick_scalar(rng: Rng) -> int:
    if rng.choice(2) == 0:
        return BOUNDARY_SCALARS[rng.choice(len(BOUNDARY_SCALARS))]
    return rng.next_u64()


def eval_scalar(op: str, a: int, b: int) -> int:
    if op == "add":
        return u64(a + b)
    if op == "sub":
        return u64(a - b)
    if op == "mul":
        return u64(a * b)
    if op == "shl":
        return u64(a << (b & 63))
    if op == "shr":
        return (a & MASK64) >> (b & 63)
    if op == "and":
        return a & b
    if op == "xor":
        return a ^ b
    raise ValueError(f"unknown op: {op}")


def gen_scalar_tree(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    if depth <= 0 or rng.choice(4) == 0:
        if rng.choice(3) == 0:
            return {"k": "var", "id": 0}, 0
        v = pick_scalar(rng)
        return {"k": "const", "v": v}, v
    op = OPS[rng.choice(len(OPS))]
    lt, lv = gen_scalar_tree(rng, depth - 1)
    rt, rv = gen_scalar_tree(rng, depth - 1)
    val = eval_scalar(op, lv, rv)
    return {"k": "binop", "op": op, "l": lt, "r": rt}, val


def gen_ite(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    cond = pick_scalar(rng)
    tt, tv = gen_expr(rng, depth - 1)
    et, ev = gen_expr(rng, depth - 1)
    val = tv if cond != 0 else ev
    return {"k": "ite", "c": cond, "t": tt, "e": et}, val


def gen_loop(rng: Rng) -> tuple[dict[str, Any], int]:
    lo = 0
    step = LOOP_STEPS[rng.choice(len(LOOP_STEPS))]
    hi = lo + step
    init_acc = pick_scalar(rng)
    addend = pick_scalar(rng)
    acc = init_acc
    for _ in range(hi - lo):
        acc = u64(acc + addend)
    return {"k": "seqFor", "lo": lo, "hi": hi, "init": init_acc, "addend": addend}, acc


def gen_expr(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    kind = rng.choice(5 if depth > 0 else 2)
    if kind == 0 or depth <= 0:
        return gen_scalar_tree(rng, max(depth, 0))
    if kind == 1:
        inner, v = gen_expr(rng, depth - 1)
        return {"k": "let", "body": inner}, v
    if kind == 2:
        return gen_ite(rng, depth)
    if kind == 3:
        return gen_loop(rng)
    return gen_scalar_tree(rng, depth)


def build_program(seed: int) -> dict[str, Any]:
    rng = Rng(splitmix64(seed))
    depth = 1 + rng.choice(3)
    arg0 = pick_scalar(rng)
    if rng.choice(6) == 0:
        data = [pick_scalar(rng) for _ in range(4)]
        exclusive = rng.choice(2) == 0
        idx = rng.choice(4)
        val = pick_scalar(rng)
        # This is only a scalar conditional, not an aliasing/RC test.
        tree = {
            "k": "ite",
            "c": 1 if exclusive else 0,
            "t": {"k": "binop", "op": "xor", "l": {"k": "const", "v": val}, "r": {"k": "var", "id": 0}},
            "e": {"k": "binop", "op": "add", "l": {"k": "const", "v": data[idx]}, "r": {"k": "var", "id": 0}},
        }
        return {
            "k": "scalar_conditional",
            "tree": tree,
            "data": data,
            "exclusive": exclusive,
            "idx": idx,
            "val": val,
            "arg0": arg0,
            "seed": seed,
        }
    tree, _ = gen_expr(rng, depth)
    return {"k": "program", "tree": tree, "arg0": arg0, "seed": seed}


def tree_to_lean_expr(node: dict[str, Any]) -> str:
    k = node["k"]
    if k == "const":
        return f"({u64(node['v'])} : UInt64)"
    if k == "var":
        return "x0"
    if k == "binop":
        l = tree_to_lean_expr(node["l"])
        r = tree_to_lean_expr(node["r"])
        op = node["op"]
        if op == "add":
            return f"({l} + {r})"
        if op == "sub":
            return f"({l} - {r})"
        if op == "mul":
            return f"({l} * {r})"
        if op == "shl":
            return f"({l} <<< ({r} &&& 63))"
        if op == "shr":
            return f"({l} >>> ({r} &&& 63))"
        if op == "and":
            return f"({l} &&& {r})"
        if op == "xor":
            return f"({l} ^^^ {r})"
    if k == "let":
        b = tree_to_lean_expr(node["body"])
        return f"(let tmp : UInt64 := {b}; tmp)"
    if k == "ite":
        t = tree_to_lean_expr(node["t"])
        e = tree_to_lean_expr(node["e"])
        c = u64(node["c"])
        return f"(if ({c} : UInt64) == 0 then {e} else {t})"
    if k == "seqFor":
        steps = node["hi"] - node["lo"]
        init_v = u64(node["init"])
        add_v = u64(node["addend"])
        terms = [f"({init_v} : UInt64)"] + [f"({add_v} : UInt64)" for _ in range(steps)]
        return "(" + " + ".join(terms) + ")"
    raise ValueError(k)


def find_lean_binary() -> str | None:
    for cand in [
        shutil.which("lean"),
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"),
        "/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
        "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
        "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean",
    ]:
        if cand and Path(cand).is_file() and os.access(cand, os.X_OK):
            try:
                prefix = subprocess.run([cand, "--print-prefix"], cwd=ROOT / "lean",
                                        check=True, capture_output=True, text=True).stdout.strip()
                pinned = Path(prefix) / "bin" / "lean"
                if pinned.is_file():
                    return str(pinned)
            except (OSError, subprocess.SubprocessError):
                continue
    return None


def find_clang_binary() -> str | None:
    for cand in [
        "/usr/bin/clang",
        "/usr/bin/clang-18",
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/clang"),
        "/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
        "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
        "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
        shutil.which("clang"),
    ]:
        if cand and Path(cand).is_file() and os.access(cand, os.X_OK):
            return cand
    return None


def clang_extra_flags(clang_bin: str) -> list[str]:
    p = Path(clang_bin).resolve()
    inc_clang = p.parent.parent / "include" / "clang"
    if inc_clang.is_dir():
        return [f"-isystem{inc_clang}"]
    return []


def probe_engines(
    override_lean: str | None = None,
    override_core: str | None = None,
    override_clang: str | None = None,
) -> dict[str, Any]:
    lean_bin = override_lean if override_lean is not None else find_lean_binary()
    core_bin = override_core if override_core is not None else str(LEAN_NATIVE_CORE)
    full_bin = str(LEAN_NATIVE_FULL) if LEAN_NATIVE_FULL.is_file() else None
    clang_bin = override_clang if override_clang is not None else find_clang_binary()
    lean_ok = bool(lean_bin and Path(lean_bin).is_file() and os.access(lean_bin, os.X_OK))
    core_ok = bool(core_bin and Path(core_bin).is_file() and os.access(core_bin, os.X_OK))
    full_ok = bool(full_bin and Path(full_bin).is_file() and os.access(full_bin, os.X_OK))
    clang_ok = bool(clang_bin and Path(clang_bin).is_file() and os.access(clang_bin, os.X_OK))
    if core_ok:
        try:
            subprocess.run([core_bin, "validate-tv", "--json"], check=True, capture_output=True, text=True)
        except (subprocess.CalledProcessError, OSError):
            core_ok = False
    return {
        "lean_bin": lean_bin if lean_ok else None,
        "core_bin": core_bin if core_ok else None,
        "full_bin": full_bin if full_ok else None,
        "clang_bin": clang_bin if clang_ok else None,
        "stock_lean_c": lean_ok and clang_ok,
        "lnir_eval": core_ok and full_ok,
        "c_abi_llvm": core_ok and full_ok and clang_ok,
    }


def run_three_way_batch(
    programs: list[dict[str, Any]],
    engines: dict[str, Any],
    mutate_engine: str | None = None,
) -> dict[str, Any]:
    """Execute ALL fuzz programs through:
      (1) stock `lean -c` + `clang` binary execution,
      (2) frontend lowering (`lean-native emit-lnir --wire`) + `lean-native-core eval-lnir --batch-json --opt` + `validate-tv`,
      (3) `lean-native-core compile-llvm` + `clang` binary execution.
    """
    lean_bin = engines["lean_bin"]
    core_bin = engines["core_bin"]
    full_bin = engines.get("full_bin")
    if not full_bin:
        raise RuntimeError("Missing real Lean frontend; core is not a substitute")
    clang_bin = engines["clang_bin"]

    if not programs:
        return {
            "executed_count": 0,
            "mismatches": [],
            "receipts": {},
        }

    with tempfile.TemporaryDirectory(prefix="turbo_c4_batch_") as tmp:
        tmpdir = Path(tmp)
        lean_lines = ["-- Auto-generated Tier C4 differential batch"]
        c_driver_decls = ["#include <stdint.h>", "#include <stdio.h>"]
        c_driver_calls = ["int main(void) {", "  printf(\"[\");"]
        arg_list_strs: list[str] = []

        for idx, p in enumerate(programs):
            seed = p["seed"]
            arg0 = u64(p["arg0"])
            fn_name = f"fuzz_seed_{seed}"
            arg_list_strs.append(f"{fn_name}:{arg0}")
            lean_expr = tree_to_lean_expr(p["tree"])
            lean_lines.append(f"@[export {fn_name}]")
            lean_lines.append(f"def {fn_name} (x0 : UInt64) : UInt64 := {lean_expr}")
            c_driver_decls.append(f"extern uint64_t {fn_name}(uint64_t);")
            sep = "," if idx > 0 else ""
            c_driver_calls.append(
                f'  printf("{sep}\\"%llu\\"", (unsigned long long){fn_name}({arg0}ULL));'
            )

        c_driver_calls.append('  printf("]\\n");')
        c_driver_calls.append("  return 0;")
        c_driver_calls.append("}")

        lean_src = "\n".join(lean_lines) + "\n"
        lean_file = tmpdir / "FuzzerBatch.lean"
        lean_c_file = tmpdir / "FuzzerBatch.lean.c"
        lean_setup = tmpdir / "FuzzerBatch.setup.json"
        lean_setup.write_text(
            json.dumps({
                "name": "FuzzerBatch",
                "isModule": False,
                "importArts": {},
                "dynlibs": [],
                "plugins": [],
                "options": {"autoImplicit": False},
                "package": "fuzzer",
            }),
            encoding="utf-8",
        )
        lean_file.write_text(lean_src, encoding="utf-8")

        # Compile the original definitions plus an IO driver with the stock runtime.
        stock_source = tmpdir / "StockOracle.lean"
        calls = [f"toString (fuzz_seed_{p['seed']} {u64(p['arg0'])})" for p in programs]
        stock_source.write_text(
            lean_src + '\ndef main : IO Unit :=\n  IO.println ("[" ++ String.intercalate "," ['
            + ", ".join(calls) + '] ++ "]")\n', encoding="utf-8"
        )
        subprocess.run(
            [lean_bin, str(stock_source), "-c", str(lean_c_file)],
            cwd=str(tmpdir),
            check=True,
            capture_output=True,
            text=True,
        )
        driver_c_path = tmpdir / "driver.c"
        stock_bin_path = tmpdir / "stock_runner"
        driver_c_path.write_text(
            "\n".join(c_driver_decls)
            + "\n"
            + "\n".join(c_driver_calls)
            + "\n",
            encoding="utf-8",
        )
        extra_inc = clang_extra_flags(clang_bin)
        lean_prefix = subprocess.run([lean_bin, "--print-prefix"], check=True, capture_output=True, text=True).stdout.strip()
        leanc = str(Path(lean_prefix) / "bin" / "leanc")
        subprocess.run(
            [leanc, "-O2", str(lean_c_file), "-o", str(stock_bin_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        stock_out = subprocess.run([str(stock_bin_path)], check=True, capture_output=True, text=True).stdout
        stock_vals = [int(x) for x in json.loads(stock_out)]
        if mutate_engine == "stock_lean_c" and stock_vals:
            stock_vals[0] = u64(stock_vals[0] ^ 1)

        # 2. Engine 2: Frontend Lowering (`lean-native emit-lnir --wire`) + `eval-lnir --batch-json` + `validate-tv`
        wire_path = tmpdir / "batch.lnir"
        subprocess.run(
            [full_bin, "emit-lnir", "--wire", str(lean_file), "-o", str(wire_path)],
            check=True,
            capture_output=True,
            text=True,
        )

        tv_out = subprocess.run(
            [core_bin, "validate-tv", "--lnir", str(wire_path), "--json"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        tv_json = json.loads(tv_out)

        ev_res = subprocess.run(
            [
                core_bin,
                "eval-lnir",
                "--lnir",
                str(wire_path),
                "--args",
                ";".join(arg_list_strs),
                "--opt",
                "--batch-json",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        ev_rows = json.loads(ev_res.stdout)
        expected_decls = {f"fuzz_seed_{p['seed']}" for p in programs}
        if (len(ev_rows) != len(programs) or any(r.get("ok") is not True for r in ev_rows)
                or {r.get("decl") for r in ev_rows} != expected_decls):
            raise RuntimeError("Evaluation did not execute each exact requested declaration once")
        ev_by_decl = {r["decl"]: int(r["value_u64"]) for r in ev_rows if r.get("ok")}
        total_live_objs = sum(int(r.get("live_objects", 0)) for r in ev_rows if r.get("ok"))
        lnir_vals: list[int] = []
        for idx, p in enumerate(programs):
            fn_name = f"fuzz_seed_{p['seed']}"
            val = ev_by_decl.get(fn_name, -1)
            if mutate_engine == "lnir_eval" and idx == len(programs) - 1:
                val = u64(val + 1)
            lnir_vals.append(val)

        # 3. Engine 3: LeanNative Compiled LLVM Native Binary (`compile-llvm` + `clang`)
        ll_path = tmpdir / "batch.ll"
        ln_bin_path = tmpdir / "ln_runner"
        subprocess.run(
            [core_bin, "compile-llvm", "--lnir", str(wire_path), "-o", str(ll_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            [clang_bin, "-O2", "-Wno-override-module", *extra_inc, str(ll_path), str(driver_c_path), "-o", str(ln_bin_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        ln_out = subprocess.run([str(ln_bin_path)], check=True, capture_output=True, text=True).stdout
        ln_vals = [int(x) for x in json.loads(ln_out)]
        if len(stock_vals) != len(programs) or len(ln_vals) != len(programs):
            raise RuntimeError("Native execution skipped or duplicated rows")
        if mutate_engine == "c_abi_llvm" and ln_vals:
            ln_vals[-1] = u64(ln_vals[-1] ^ 0xDEAD)

        mismatches = []
        if not tv_json.get("allPassed", False):
            mismatches.append({"seed": -1, "kind": "validate_tv_failed", "detail": tv_json})
        for idx, p in enumerate(programs):
            sv = stock_vals[idx]
            lv = lnir_vals[idx]
            nv = ln_vals[idx]
            if sv != lv or lv != nv:
                mismatches.append({
                    "seed": p["seed"],
                    "kind": p["tree"]["k"],
                    "stock_lean_c": str(sv),
                    "lnir_eval": str(lv),
                    "c_abi_llvm": str(nv),
                })

        receipts = {
            "lean_source_sha256": sha256_bytes(lean_file.read_bytes()),
            "stock_source_sha256": sha256_bytes(stock_source.read_bytes()),
            "stock_unmodified_c_sha256": sha256_bytes(lean_c_file.read_bytes()),
            "stock_runtime": "stock lean -c + leanc (full generated C, no replacements)",
            "lnir_wire_sha256": sha256_bytes(wire_path.read_bytes()),
            "llvm_ir_sha256": sha256_bytes(ll_path.read_bytes()),
            "stock_binary_sha256": sha256_bytes(stock_bin_path.read_bytes()),
            "leannative_binary_sha256": sha256_bytes(ln_bin_path.read_bytes()),
            "symbolic_tv_passed_decls": tv_json.get("passedDecls", 0),
            "lnir_eval_executed_decls": len(ev_by_decl),
        }
        return {
            "executed_count": len(programs),
            "mismatches": mismatches,
            "live_objects": total_live_objs,
            "receipts": receipts,
        }


def run_fuzzer(
    num_seeds: int = 50,
    override_lean: str | None = None,
    override_core: str | None = None,
    override_clang: str | None = None,
    mutate_engine: str | None = None,
) -> dict[str, Any]:
    n = max(0, num_seeds)
    engines = probe_engines(override_lean, override_core, override_clang)
    all_engines_ready = (
        engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]
    )
    if not all_engines_ready:
        return {
            "schemaVersion": "turbo-lean-lcnf-fuzz-v2",
            "tier": "C4",
            "status": "incomplete_missing_engine",
            "ok": False,
            "seeds": n,
            "checked": 0,
            "mismatch_count": 0,
            "rc_leak_count": None,
            "coverage": "scalar_only_no_alias_rc_or_seqFor",
            "parity": "incomplete",
            "engines": {
                "stock_lean_c": engines["stock_lean_c"],
                "lnir_validate_tv": engines["lnir_eval"],
                "c_abi_llvm": engines["c_abi_llvm"],
            },
            "boundary_scalars": list(BOUNDARY_SCALARS),
            "shrunk_failures": [{"error": "Required conformance engines unavailable; refusing to report pass"}],
        }

    programs = [build_program(seed) for seed in range(n)]
    mismatches = 0
    failures: list[dict[str, Any]] = []
    try:
        batch_res = run_three_way_batch(programs, engines, mutate_engine=mutate_engine)
    except (subprocess.SubprocessError, OSError, ValueError, RuntimeError) as exc:
        batch_res = {"executed_count": 0, "mismatches": [], "receipts": {}}
        failures.append({"error": str(exc), "stderr": getattr(exc, "stderr", None)})
    mismatches += len(batch_res["mismatches"])
    failures.extend(batch_res["mismatches"])

    checked = batch_res["executed_count"]
    parity_ok = n > 0 and checked == n and mismatches == 0 and not failures
    return {
        "schemaVersion": "turbo-lean-lcnf-fuzz-v2",
        "tier": "C4",
        "status": "passed_scalar_only" if parity_ok else "failed_or_incomplete",
        "coverage": "scalar_only_no_alias_rc_or_seqFor",
        "ok": parity_ok,
        "seeds": n,
        "checked": checked,
        "mismatch_count": mismatches,
        "rc_leak_count": None,
        "interpreter_live_objects": batch_res.get("live_objects"),
        "parity": "100%" if (parity_ok and n > 0) else f"{checked - mismatches}/{checked}",
        "engines": {
            "stock_lean_c": engines["stock_lean_c"],
            "lnir_validate_tv": engines["lnir_eval"],
            "c_abi_llvm": engines["c_abi_llvm"],
        },
        "receipts": batch_res["receipts"],
        "boundary_scalars": list(BOUNDARY_SCALARS),
        "shrunk_failures": failures[:8],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Tier C4 LCNF/LNIR differential fuzzer")
    ap.add_argument("--seeds", type=int, default=64, help="Number of deterministic seeds")
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    ap.add_argument("--mutate-engine", type=str, default=None, help="Inject mutation into stock_lean_c|lnir_eval|c_abi_llvm")
    args = ap.parse_args()
    report = run_fuzzer(args.seeds, mutate_engine=args.mutate_engine)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        status = "PASSED" if report["ok"] else f"FAILED ({report['status']})"
        print(
            f"[fuzz-lcnf] {status} seeds={report['seeds']} checked={report['checked']} "
            f"mismatches={report['mismatch_count']} rc_leaks={report['rc_leak_count']} "
            f"stock_lean={report['engines']['stock_lean_c']} "
            f"tv={report['engines']['lnir_validate_tv']} "
            f"clang={report['engines']['c_abi_llvm']}"
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
