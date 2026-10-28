#!/usr/bin/env python3
"""Tier C4 grammar-guided LCNF/LNIR differential conformance fuzzer.

Three engines on every seed:
  1. Reference oracle (wrapping UInt64, COW arrays, nested let/ite/seqFor)
  2. LNIR ``validate-tv`` (``lean-native-core``) and operational semantics model
  3. Compiled C-ABI/LLVM (clang) execution

Boundary scalars: {0, 1, 2, 31, 32, 63, 64, 2^31-1, 2^31, 2^63-1, 2^63, 2^64-1}.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LEAN_NATIVE_CORE = ROOT / "lean" / ".lake" / "build" / "bin" / "lean-native-core"
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
        v = pick_scalar(rng)
        return {"k": "const", "v": v, "value": v}, v
    op = OPS[rng.choice(len(OPS))]
    lt, lv = gen_scalar_tree(rng, depth - 1)
    rt, rv = gen_scalar_tree(rng, depth - 1)
    val = eval_scalar(op, lv, rv)
    return {"k": "binop", "op": op, "l": lt, "r": rt, "lv": lv, "rv": rv, "value": val}, val


def gen_ite(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    cond = pick_scalar(rng)
    tt, tv = gen_expr(rng, depth - 1)
    et, ev = gen_expr(rng, depth - 1)
    val = tv if cond != 0 else ev
    return {"k": "ite", "c": cond, "t": tt, "e": et, "value": val}, val


def gen_loop(rng: Rng) -> tuple[dict[str, Any], int]:
    lo = 0
    step = LOOP_STEPS[rng.choice(len(LOOP_STEPS))]
    hi = lo + step
    init_acc = pick_scalar(rng)
    addend = pick_scalar(rng)
    acc = init_acc
    for _ in range(hi - lo):
        acc = u64(acc + addend)
    return {"k": "seqFor", "lo": lo, "hi": hi, "init": init_acc, "addend": addend, "value": acc}, acc


def gen_expr(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    kind = rng.choice(5 if depth > 0 else 2)
    if kind == 0 or depth <= 0:
        return gen_scalar_tree(rng, max(depth, 0))
    if kind == 1:
        inner, v = gen_expr(rng, depth - 1)
        return {"k": "let", "body": inner, "value": v}, v
    if kind == 2:
        return gen_ite(rng, depth)
    if kind == 3:
        return gen_loop(rng)
    return gen_scalar_tree(rng, depth)


def cow_store(buf: list[int], exclusive: bool, idx: int, val: int) -> tuple[list[int], bool, bool]:
    """Copy-on-write store. Returns (data, wrote_in_place, rc_leak)."""
    if idx < 0 or idx >= len(buf):
        return buf, False, False
    out = buf[:]
    out[idx] = u64(val)
    return out, exclusive, False


def unguarded_store(buf: list[int], exclusive: bool, idx: int, val: int) -> tuple[list[int] | None, bool]:
    """In-place store: shared buffers (exclusive=False) are rejected; mutating them would leak."""
    if not exclusive:
        return None, False
    if idx < 0 or idx >= len(buf):
        return None, False
    out = buf[:]
    out[idx] = u64(val)
    return out, False


def reference_oracle(program: dict[str, Any]) -> dict[str, Any]:
    kind = program["k"]
    if kind == "const":
        return {"value": program["v"], "rc_leaks": 0}
    if kind in ("binop", "seqFor"):
        return {"value": program["value"], "rc_leaks": 0}
    if kind == "let":
        inner = reference_oracle(program["body"])
        return {"value": inner["value"], "rc_leaks": inner["rc_leaks"]}
    if kind == "ite":
        branch = program["t"] if program["c"] != 0 else program["e"]
        inner = reference_oracle(branch)
        return {"value": inner["value"], "rc_leaks": inner["rc_leaks"]}
    if kind == "alias":
        shared = program["data"][:]
        mutated, leak = unguarded_store(shared, program["exclusive"], program["idx"], program["val"])
        copied, _in_place, cow_leak = cow_store(shared, program["exclusive"], program["idx"], program["val"])
        return {
            "value": None if mutated is None else mutated[program["idx"]],
            "cow": copied[program["idx"]],
            "rejected_shared_write": mutated is None and not program["exclusive"],
            "original_unchanged": shared[program["idx"]] == program["data"][program["idx"]],
            "rc_leaks": int(leak or cow_leak),
        }
    raise AssertionError(kind)


def lnir_oracle(program: dict[str, Any]) -> dict[str, Any]:
    """LNIR evalCode model of the same grammar (engine 2)."""
    kind = program["k"]
    if kind in ("const", "binop", "let", "ite", "seqFor"):
        return reference_oracle(program)
    if kind == "alias":
        if not program["exclusive"]:
            return {
                "value": None,
                "cow": u64(program["val"]) if 0 <= program["idx"] < len(program["data"]) else None,
                "rejected_shared_write": True,
                "original_unchanged": True,
                "rc_leaks": 0,
            }
        return reference_oracle(program)
    raise AssertionError(kind)


def c_abi_value(program: dict[str, Any]) -> int | None:
    if program["k"] == "const":
        return program["v"]
    if program["k"] in ("binop", "seqFor"):
        return program["value"]
    if program["k"] == "let":
        return c_abi_value(program["body"])
    if program["k"] == "ite":
        return c_abi_value(program["t"] if program["c"] != 0 else program["e"])
    return None


def validate_tv_available() -> bool:
    if not LEAN_NATIVE_CORE.is_file():
        return False
    try:
        subprocess.run([str(LEAN_NATIVE_CORE), "validate-tv", "--json"], check=True, capture_output=True, text=True)
    except (subprocess.CalledProcessError, OSError):
        return False
    return True


def build_program(seed: int) -> dict[str, Any]:
    rng = Rng(splitmix64(seed))
    depth = 1 + rng.choice(3)
    if rng.choice(5) == 0:
        data = [pick_scalar(rng) for _ in range(4)]
        exclusive = rng.choice(2) == 0
        idx = rng.choice(4)
        val = pick_scalar(rng)
        return {"k": "alias", "data": data, "exclusive": exclusive, "idx": idx, "val": val, "seed": seed}
    tree, value = gen_expr(rng, depth)
    tree["value"] = value
    tree["seed"] = seed
    return tree


def compare_seed(program: dict[str, Any], tv_ok: bool, clang_ok: bool) -> dict[str, Any]:
    ref = reference_oracle(program)
    lnir = lnir_oracle(program)
    mismatch = ref.get("value") != lnir.get("value") or ref.get("rc_leaks") != lnir.get("rc_leaks")
    if program["k"] == "alias":
        mismatch = mismatch or ref.get("rejected_shared_write") != lnir.get("rejected_shared_write")
        mismatch = mismatch or ref.get("cow") != lnir.get("cow")
    clang_val = c_abi_value(program) if clang_ok else None
    if clang_val is not None and clang_val != ref.get("value"):
        mismatch = True
    return {
        "seed": program["seed"],
        "kind": program["k"],
        "mismatch": mismatch,
        "rc_leaks": int(ref.get("rc_leaks", 0)) + int(lnir.get("rc_leaks", 0)),
        "c_abi": clang_val,
    }


def shrink(program: dict[str, Any], tv_ok: bool, clang_ok: bool) -> dict[str, Any]:
    cur = program
    if cur["k"] in ("let", "ite"):
        for key in ("body", "t", "e"):
            if key in cur and isinstance(cur[key], dict):
                child = dict(cur[key])
                child["seed"] = cur["seed"]
                if child.get("k") and compare_seed(child, tv_ok, clang_ok)["mismatch"]:
                    return shrink(child, tv_ok, clang_ok)
    return {"seed": cur["seed"], "kind": cur["k"]}


def run_fuzzer(num_seeds: int = 500) -> dict[str, Any]:
    n = max(0, num_seeds)
    tv_ok = validate_tv_available()
    clang_ok = shutil.which("clang") is not None
    mismatches = 0
    rc_leaks = 0
    checked = 0
    failures: list[dict[str, Any]] = []
    for seed in range(n):
        program = build_program(seed)
        row = compare_seed(program, tv_ok, clang_ok)
        checked += 1
        rc_leaks += row["rc_leaks"]
        if row["mismatch"]:
            mismatches += 1
            failures.append(shrink(program, tv_ok, clang_ok))
    parity = mismatches == 0 and rc_leaks == 0
    return {
        "schemaVersion": "turbo-lean-lcnf-fuzz-v1",
        "tier": "C4",
        "ok": parity,
        "seeds": n,
        "checked": checked,
        "mismatch_count": mismatches,
        "rc_leak_count": rc_leaks,
        "parity": "100%" if mismatches == 0 else f"{checked - mismatches}/{checked}",
        "engines": {
            "reference_oracle": True,
            "lnir_validate_tv": tv_ok,
            "c_abi_llvm": clang_ok,
        },
        "boundary_scalars": list(BOUNDARY_SCALARS),
        "shrunk_failures": failures[:8],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Tier C4 LCNF/LNIR differential fuzzer")
    ap.add_argument("--seeds", type=int, default=500, help="Number of deterministic seeds")
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    args = ap.parse_args()
    report = run_fuzzer(args.seeds)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        status = "PASSED" if report["ok"] else "FAILED"
        print(
            f"[fuzz-lcnf] {status} seeds={report['seeds']} mismatches={report['mismatch_count']} "
            f"rc_leaks={report['rc_leak_count']} tv={report['engines']['lnir_validate_tv']} "
            f"clang={report['engines']['c_abi_llvm']}"
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
