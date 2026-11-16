#!/usr/bin/env python3
"""Differential conformance probe (scalar 3-way + alias 2-way), not full Tier C4 acceptance.

Executes THREE genuinely independent engines on EVERY scalar seed and corpus program:
  1. Engine 1 (`stock_lean_c`): Elaborates & compiles the generated `.lean` source file with
     the stock Lean 4 compiler (`lean -c` + `leanc`) and its unmodified runtime.
  2. Engine 2 (`lnir_eval`): Lowers the same `.lean` program to `LNIR` via the real compiler
     frontend (`lean-native emit-lnir --wire <FuzzerBatch.lean>`) and evaluates EVERY declaration
     with the formal operational interpreter (`lean-native-core eval-lnir --batch-json --opt`),
     plus the repository's symbolic translation validator (`lean-native-core validate-tv`).
  3. Engine 3 (`leannative_llvm_binary`): Compiles the lowered `LNIRModule` through `LeanNative`'s
     LLVM backend (`lean-native-core compile-llvm`) and `clang` into a native executable and runs it.

Alias tier (C4x): every `seed % 6 == 0` seed above 3 generates a GENUINE alias program — a small
non-recursive RC inductive (`FuzzPacket`) with two live names for the same heap object, in a
shared (`foo a a`: one object, two uses) and an exclusive (two distinct objects) variant — the
repository's proven Stage 1D shape. A wrong reference count (an in-place update observed through
the old name) or a premature free becomes an observable value difference or a leaked object:
  - Alias programs run TWO-way: stock Lean C vs `emit-lnir --allow-rc-adt` + `eval-lnir` +
    `validate-tv`. `compile-llvm` of heap decls must fail closed (asserted per batch; if a future
    backend accepts them the tier upgrades to three-way automatically).
  - Every alias eval row must report `live_objects == 0`; leaks are counted in `rc_leak_count`.
  - `alias_program_count` (with shared/exclusive split) is measured, printed, and held above a
    stated floor (`>= num_seeds // 8`); a run under the floor fails closed. Passing seeds never
    silently mean aliasing coverage.

Hard Fail-Closed Contract (`P0`/`P1`):
  - If ANY required engine (`lean`, `lean-native`, `lean-native-core`, `clang`) is missing or not
    executable, `run_fuzzer` returns `ok: False, status: "incomplete_missing_engine"` and exits non-zero.
  - Precomputed `program["value"]` or Python-only fallback is NEVER used as an engine output.
   - Loop-shaped cases are unrolled additions. LNIR seqFor with nonzero trip count is not exercised.
  - Every batch execution records SHA-256 digests of the `.lean` source, frontend-lowered `.lnir`,
   emitted `.ll`, and compiled binaries in the receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
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
    7,
    8,
    15,
    16,
    31,
    32,
    63,
    64,
    255,
    256,
    65535,
    65536,
    (1 << 31) - 1,
    1 << 31,
    (1 << 32) - 1,
    1 << 32,
    (1 << 63) - 1,
    1 << 63,
    (1 << 64) - 1,
)
LOOP_STEPS: tuple[int, ...] = (0, 1, 2, 7)
OPS = ("add", "sub", "mul", "div", "mod", "shl", "shr", "and", "or", "xor")
WIDTHS = (8, 16, 32, 64)
CMP_OPS = ("==", "!=", "<", "<=")


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
    if op == "div":
        return 0 if u64(b) == 0 else u64(a) // u64(b)
    if op == "mod":
        return u64(a) if u64(b) == 0 else u64(a) % u64(b)
    if op == "shl":
        return u64(a << (b & 63))
    if op == "shr":
        return (a & MASK64) >> (b & 63)
    if op == "and":
        return a & b
    if op == "or":
        return a | b
    if op == "xor":
        return a ^ b
    raise ValueError(f"unknown op: {op}")


def gen_scalar_tree(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    if depth <= 0 or rng.choice(4) == 0:
        if rng.choice(3) == 0:
            return {"k": "var", "id": 0}, 0
        v = pick_scalar(rng)
        return {"k": "const", "v": v}, v
    kind = rng.choice(7)
    if kind == 0:
        src = WIDTHS[rng.choice(len(WIDTHS))]
        dst_choices = [w for w in WIDTHS if w != src]
        dst = dst_choices[rng.choice(len(dst_choices))]
        sub, _ = gen_scalar_tree(rng, depth - 1)
        return {"k": "uint_cast", "src_bits": src, "dst_bits": dst, "arg": sub}, 0
    if kind == 1:
        w = (8, 16, 32)[rng.choice(3)]
        op = OPS[rng.choice(len(OPS))]
        lt, _ = gen_scalar_tree(rng, depth - 1)
        rt, _ = gen_scalar_tree(rng, depth - 1)
        return {"k": "narrow_binop", "bits": w, "op": op, "l": lt, "r": rt}, 0
    if kind == 2:
        op = OPS[rng.choice(len(OPS))]
        lt, _ = gen_scalar_tree(rng, depth - 1)
        rt, _ = gen_scalar_tree(rng, depth - 1)
        return {"k": "usize_binop", "op": op, "l": lt, "r": rt}, 0
    if kind == 3:
        w = WIDTHS[rng.choice(len(WIDTHS))]
        sub, _ = gen_scalar_tree(rng, depth - 1)
        return {"k": "complement", "bits": w, "arg": sub}, 0
    op = OPS[rng.choice(len(OPS))]
    lt, lv = gen_scalar_tree(rng, depth - 1)
    rt, rv = gen_scalar_tree(rng, depth - 1)
    val = eval_scalar(op, lv, rv)
    return {"k": "binop", "op": op, "l": lt, "r": rt}, val


def gen_ite(rng: Rng, depth: int) -> tuple[dict[str, Any], int]:
    tt, tv = gen_expr(rng, depth - 1)
    et, ev = gen_expr(rng, depth - 1)
    if rng.choice(2) == 0:
        cond = pick_scalar(rng)
        val = tv if cond != 0 else ev
        return {"k": "ite", "c": cond, "t": tt, "e": et}, val
    op1 = CMP_OPS[rng.choice(len(CMP_OPS))]
    op2 = CMP_OPS[rng.choice(len(CMP_OPS))]
    comb = ("&&", "||", "!=", "==")[rng.choice(4)]
    b1 = pick_scalar(rng)
    b2 = pick_scalar(rng)
    neg = rng.choice(2) == 1
    return {
        "k": "bool_branch",
        "op1": op1,
        "b1": b1,
        "op2": op2,
        "b2": b2,
        "comb": comb,
        "neg": neg,
        "t": tt,
        "e": et,
    }, 0


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
    kind = rng.choice(6 if depth > 0 else 2)
    if kind == 0 or depth <= 0:
        return gen_scalar_tree(rng, max(depth, 0))
    if kind == 1:
        inner, v = gen_expr(rng, depth - 1)
        return {"k": "let", "body": inner}, v
    if kind == 2:
        return gen_ite(rng, depth)
    if kind == 3:
        return gen_loop(rng)
    if kind == 4:
        b1 = pick_scalar(rng)
        b2 = pick_scalar(rng)
        c1 = pick_scalar(rng)
        c2 = pick_scalar(rng)
        return {"k": "multi_jp", "b1": b1, "b2": b2, "c1": c1, "c2": c2}, 0
    return gen_scalar_tree(rng, depth)


ALIAS_SEED_MOD = 6
ALIAS_FLOOR_RATIO = 8
ALIAS_PREAMBLE = """inductive FuzzPacket where
  | pkt : (UInt64 × UInt64) → (UInt64 × UInt64) → FuzzPacket
  | empty : FuzzPacket

@[inline] def fuzzPacketFold (pkt : FuzzPacket) : UInt64 :=
  match pkt with
  | .pkt p q => ((p.1 * 1315423911) + p.2) ^^^ ((q.1 * 2654435761) + q.2)
  | .empty => 0x9E3779B97F4A7C15

@[inline] def fuzzPacketStep (pkt : FuzzPacket) (delta : UInt64) : FuzzPacket :=
  match pkt with
  | .pkt p q => .pkt (p.1 + delta, p.2 ^^^ delta) (q.1 + (delta <<< 1), q.2 + 17)
  | .empty => .empty

@[inline] def fuzzP1 (pkt : FuzzPacket) : UInt64 := match pkt with | .pkt p _ => p.1 | .empty => 0
@[inline] def fuzzP2 (pkt : FuzzPacket) : UInt64 := match pkt with | .pkt p _ => p.2 | .empty => 0
@[inline] def fuzzQ1 (pkt : FuzzPacket) : UInt64 := match pkt with | .pkt _ q => q.1 | .empty => 0
@[inline] def fuzzQ2 (pkt : FuzzPacket) : UInt64 := match pkt with | .pkt _ q => q.2 | .empty => 0
"""


def gen_alias_program(seed: int) -> dict[str, Any]:
    """A genuine alias program: two live names for one heap object.

    `alias_shared` selects the shared variant (one object read through two names,
    the `foo arr arr` shape) or the exclusive variant (two distinct objects). The
    step applied through the second name is a reset/reuse decision point: a wrong
    reference count mutates the shared object in place, which the canary reads
    (`old_read`) and the combined value (`ret`) observe; a premature free or a
    cross-object corruption shows up as a value difference or a leaked object.
    """
    rng = Rng(splitmix64(seed ^ 0xA11A5A11A5A5A5A5))
    shared = (seed // ALIAS_SEED_MOD) % 2 == 0
    idx = rng.choice(4)
    jdx = rng.choice(4)
    val = pick_scalar(rng)
    c1 = pick_scalar(rng)
    c2 = pick_scalar(rng)
    arg0 = pick_scalar(rng)
    return {
        "k": "alias_program",
        "seed": seed,
        "arg0": arg0,
        "alias_shared": shared,
        "alias_probe": {"idx": idx, "jdx": jdx, "val": u64(val), "c1": u64(c1), "c2": u64(c2)},
        "preamble": ALIAS_PREAMBLE,
    }


def program_contains_alias(program: dict[str, Any]) -> bool:
    """True only for programs with two live names for one heap object."""
    return program.get("k") == "alias_program"


def alias_observations_differ(a: dict[str, Any], b: dict[str, Any]) -> bool:
    return any(a.get(k) != b.get(k) for k in ("ret", "old_read", "new_read"))


def alias_mismatch(
    program: dict[str, Any],
    stock_obs: dict[str, Any],
    lnir_obs: dict[str, Any],
    llvm_obs: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    """A mismatch record when any alias observation differs between engines."""
    differ = alias_observations_differ(stock_obs, lnir_obs) or (
        llvm_obs is not None and alias_observations_differ(stock_obs, llvm_obs)
    )
    if not differ:
        return None
    record = {
        "seed": program["seed"],
        "kind": program["k"],
        "alias_shared": program.get("alias_shared"),
        "stock_lean_c": {k: str(v) for k, v in stock_obs.items()},
        "lnir_eval": {k: str(v) for k, v in lnir_obs.items()},
    }
    if llvm_obs is not None:
        record["c_abi_llvm"] = {k: str(v) for k, v in llvm_obs.items()}
    return record


def build_program(seed: int) -> dict[str, Any]:
    if seed == 0:
        return {
            "k": "program",
            "tree": {"k": "binop", "op": "sub", "l": {"k": "const", "v": 19}, "r": {"k": "var", "id": 0}},
            "arg0": 7,
            "seed": seed,
        }
    if seed == 1:
        return {
            "k": "program",
            "tree": {"k": "ite_input", "op": "<", "bits": 64, "boundary": 42},
            "arg0": 42,
            "seed": seed,
        }
    if seed == 2:
        zero_rhs = {"k": "binop", "op": "xor", "l": {"k": "var", "id": 0}, "r": {"k": "var", "id": 0}}
        return {
            "k": "program",
            "tree": {"k": "binop", "op": "div", "l": {"k": "var", "id": 0}, "r": zero_rhs},
            "arg0": 13,
            "seed": seed,
        }
    if seed == 3:
        return {
            "k": "program",
            "tree": {"k": "binop", "op": "shl", "l": {"k": "var", "id": 0}, "r": {"k": "const", "v": 3}},
            "arg0": 5,
            "seed": seed,
        }
    if seed % ALIAS_SEED_MOD == 0:
        return gen_alias_program(seed)
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
    if k == "uint_cast":
        expr = tree_to_lean_expr(node["arg"])
        for width in (node["src_bits"], node["dst_bits"], 64):
            if width not in (8, 16, 32, 64):
                raise ValueError("unsupported unsigned width")
        if node["src_bits"] != 64:
            expr = f"({expr}).toUInt{node['src_bits']}"
        expr = f"({expr}).toUInt{node['dst_bits']}"
        return expr if node["dst_bits"] == 64 else f"({expr}).toUInt64"
    if k == "raw_lean":
        return node["expr"]
    if k == "ite_input":
        op = node.get("op", "==")
        if op not in ("==", "!=", "<", "<="):
            raise ValueError("unsupported input comparison")
        bits = node.get("bits", 64)
        if bits not in (8, 16, 32, 64):
            raise ValueError("unsupported unsigned width")
        lhs = "x0" if bits == 64 else f"x0.toUInt{bits}"
        return f"(if {lhs} {op} ({node['boundary']} : UInt{bits}) then x0 + 7 else x0 ^^^ 19)"
    if k == "narrow_binop":
        bits = node["bits"]
        if bits not in (8, 16, 32):
            raise ValueError("unsupported narrow width")
        l = f"({tree_to_lean_expr(node['l'])}).toUInt{bits}"
        r = f"({tree_to_lean_expr(node['r'])}).toUInt{bits}"
        op = node["op"]
        op_map = {
            "add": "+",
            "sub": "-",
            "mul": "*",
            "div": "/",
            "mod": "%",
            "shl": "<<<",
            "shr": ">>>",
            "and": "&&&",
            "or": "|||",
            "xor": "^^^",
        }
        return f"(({l} {op_map[op]} {r}) : UInt{bits}).toUInt64"
    if k == "usize_binop":
        l = f"({tree_to_lean_expr(node['l'])}).toUSize"
        r = f"({tree_to_lean_expr(node['r'])}).toUSize"
        op = node["op"]
        op_map = {
            "add": "+",
            "sub": "-",
            "mul": "*",
            "div": "/",
            "mod": "%",
            "shl": "<<<",
            "shr": ">>>",
            "and": "&&&",
            "or": "|||",
            "xor": "^^^",
        }
        return f"(({l} {op_map[op]} {r}) : USize).toUInt64"
    if k == "complement":
        bits = node["bits"]
        sub = tree_to_lean_expr(node["arg"])
        if bits == 64:
            return f"(~~~({sub}))"
        return f"(~~~(({sub}).toUInt{bits})).toUInt64"
    if k == "bool_branch":
        c1 = f"(x0 {node['op1']} ({u64(node['b1'])} : UInt64))"
        c2 = f"((x0 ^^^ (0x55AA : UInt64)) {node['op2']} ({u64(node['b2'])} : UInt64))"
        comb = f"({c1} {node['comb']} {c2})"
        cond = f"(!{comb})" if node.get("neg") else comb
        t = tree_to_lean_expr(node["t"])
        e = tree_to_lean_expr(node["e"])
        return f"(if {cond} then {t} else {e})"
    if k == "multi_jp":
        b1 = u64(node["b1"])
        b2 = u64(node["b2"])
        c1 = u64(node["c1"])
        c2 = u64(node["c2"])
        return (
            f"(let y : UInt64 := if x0 < ({b1} : UInt64) then x0 + ({c1} : UInt64) "
            f"else if x0 == ({b2} : UInt64) then x0 ^^^ ({c2} : UInt64) "
            f"else (x0.toUInt16 + (13 : UInt16)).toUInt64; (y * (3 : UInt64)) ^^^ (y >>> (5 : UInt64)))"
        )
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
        if op == "div":
            return f"({l} / {r})"
        if op == "mod":
            return f"({l} % {r})"
        if op == "shl":
            return f"({l} <<< {r})"
        if op == "shr":
            return f"({l} >>> {r})"
        if op == "and":
            return f"({l} &&& {r})"
        if op == "or":
            return f"({l} ||| {r})"
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


def sanitizer_flag_list(asan: bool, ubsan: bool) -> list[str]:
    sanitizers = []
    if asan:
        sanitizers.append("address")
    if ubsan:
        sanitizers.append("undefined")
    if not sanitizers:
        return []
    return [f"-fsanitize={','.join(sanitizers)}", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]


def _strip_ir_quotes_and_parens(text: str) -> str:
    no_quotes = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    prev = None
    cur = no_quotes
    while prev != cur:
        prev = cur
        cur = re.sub(r"\([^()]*\)", "()", cur)
    return cur


def _extract_define_attr_groups_and_inline(define_line: str) -> tuple[list[str], bool]:
    m = re.match(r"^define\b(.*)\{\s*$", define_line)
    if not m:
        raise RuntimeError(f"ASan instrumentation refused: malformed LLVM define header: {define_line}")
    scrubbed = _strip_ir_quotes_and_parens(m.group(1))
    groups = re.findall(r"#(\d+)\b", scrubbed)
    has_inline = bool(re.search(r"\bsanitize_address\b", scrubbed))
    return groups, has_inline


def instrument_llvm_ir_for_asan(ir_text: str) -> str:
    raw_lines = ir_text.splitlines()
    define_indices: list[int] = []
    needed_groups: set[str] = set()
    bare_define_indices: set[int] = set()

    for idx, line in enumerate(raw_lines):
        if re.match(r"^define\b", line):
            define_indices.append(idx)
            groups, has_inline = _extract_define_attr_groups_and_inline(line)
            if groups:
                needed_groups.update(groups)
            elif not has_inline:
                bare_define_indices.add(idx)

    if not define_indices:
        raise RuntimeError("ASan instrumentation refused: LLVM IR module contains zero function definitions")

    out_lines: list[str] = []
    seen_groups: dict[str, str] = {}
    for idx, line in enumerate(raw_lines):
        gm = re.match(r"^(attributes #(\d+)\s*=\s*\{)(.*)(\}\s*)$", line)
        if gm:
            gid = gm.group(2)
            if gid in seen_groups:
                raise RuntimeError(f"ASan instrumentation refused: duplicate LLVM attribute group #{gid}")
            body = gm.group(3)
            if gid in needed_groups and not re.search(r"\bsanitize_address\b", _strip_ir_quotes_and_parens(body)):
                stripped = body.strip()
                body = f" sanitize_address {stripped} " if stripped else " sanitize_address "
                line = f"{gm.group(1)}{body}{gm.group(4)}"
            seen_groups[gid] = body
        elif idx in bare_define_indices:
            line = re.sub(r"\{\s*$", "sanitize_address {", line, count=1)
        out_lines.append(line)

    missing_groups = sorted(needed_groups - set(seen_groups.keys()))
    if missing_groups:
        raise RuntimeError(f"ASan instrumentation refused: missing LLVM attribute groups #{', #'.join(missing_groups)}")

    for idx in define_indices:
        groups, has_inline = _extract_define_attr_groups_and_inline(out_lines[idx])
        if not has_inline and not (groups and all(
            re.search(r"\bsanitize_address\b", _strip_ir_quotes_and_parens(seen_groups[g])) for g in groups
        )):
            raise RuntimeError(f"ASan instrumentation failed to cover LLVM define header: {out_lines[idx]}")

    return "\n".join(out_lines) + ("\n" if ir_text.endswith("\n") else "")


def find_sanitizer_linker(clang_bin: str | None, extra_inc: list[str], asan: bool, ubsan: bool) -> str | None:
    san_flags = sanitizer_flag_list(asan, ubsan)
    if not san_flags or not clang_bin:
        return clang_bin
    with tempfile.TemporaryDirectory(prefix="turbo_san_probe_") as tmp:
        probe_dir = Path(tmp)
        probe_ll = probe_dir / "probe.ll"
        probe_c = probe_dir / "probe.c"
        probe_obj = probe_dir / "probe.san.o"
        probe_bin = probe_dir / "probe"
        raw_ll = (
            "define dso_local i64 @turbo_san_probe_fn(i64 %x) #0 {\n"
            "entry:\n"
            "  %slot = alloca [2 x i64], align 8\n"
            "  store i64 %x, ptr %slot, align 8\n"
            "  %v = load i64, ptr %slot, align 8\n"
            "  ret i64 %v\n"
            "}\n"
            "attributes #0 = { nounwind uwtable }\n"
        )
        probe_ll.write_text(instrument_llvm_ir_for_asan(raw_ll) if asan else raw_ll, encoding="utf-8")
        probe_c.write_text(
            "#include <stdint.h>\n"
            "extern uint64_t turbo_san_probe_fn(uint64_t);\n"
            "int main(void) { return turbo_san_probe_fn(42ULL) == 42ULL ? 0 : 1; }\n",
            encoding="utf-8",
        )
        cands = [
            clang_bin,
            "/usr/bin/clang",
            "/usr/bin/clang-19",
            "/usr/bin/clang-18",
            shutil.which("gcc"),
            "/usr/bin/gcc",
        ]
        probe_env = dict(os.environ)
        if asan:
            probe_env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=1:halt_on_error=1"
        if ubsan:
            probe_env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
        seen: set[str] = set()
        for cand in cands:
            if not cand or cand in seen:
                continue
            seen.add(cand)
            if not (Path(cand).is_file() and os.access(cand, os.X_OK)):
                continue
            if cand == clang_bin:
                res = subprocess.run(
                    [clang_bin, "-O1", "-g", "-Wno-override-module", *extra_inc, *san_flags, str(probe_ll), str(probe_c), "-o", str(probe_bin)],
                    capture_output=True,
                    text=True,
                )
            else:
                comp = subprocess.run(
                    [clang_bin, "-O1", "-g", "-Wno-override-module", *extra_inc, *san_flags, "-c", str(probe_ll), "-o", str(probe_obj)],
                    capture_output=True,
                    text=True,
                )
                if comp.returncode != 0 or not probe_obj.is_file():
                    continue
                res = subprocess.run(
                    [cand, "-O1", "-g", *san_flags, str(probe_obj), str(probe_c), "-o", str(probe_bin)],
                    capture_output=True,
                    text=True,
                )
            if res.returncode == 0 and probe_bin.is_file():
                run = subprocess.run([str(probe_bin)], env=probe_env, capture_output=True, text=True)
                if run.returncode == 0:
                    return cand
    return None


def compile_and_link_llvm_driver(
    clang_bin: str,
    extra_inc: list[str],
    ll_path: Path,
    driver_c_path: Path,
    out_bin_path: Path,
    asan: bool = False,
    ubsan: bool = False,
    sanitizer_linker: str | None = None,
) -> dict[str, Any]:
    san_flags = sanitizer_flag_list(asan, ubsan)
    if not san_flags:
        subprocess.run(
            [clang_bin, "-O2", "-Wno-override-module", *extra_inc, str(ll_path), str(driver_c_path), "-o", str(out_bin_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        return {
            "asan": False,
            "ubsan": False,
            "ubsan_scope": "disabled",
            "compiled_llvm_ir_sha256": sha256_bytes(ll_path.read_bytes()),
            "compiler": clang_bin,
            "linker": clang_bin,
        }

    linker = sanitizer_linker or find_sanitizer_linker(clang_bin, extra_inc, asan, ubsan)
    if not linker:
        raise RuntimeError("Requested ASan/UBSan runtime unavailable; refusing to report sanitizer pass")

    compile_ll_path = ll_path
    if asan:
        san_ll_path = ll_path.with_name(ll_path.stem + ".asan.ll")
        san_ll_path.write_text(instrument_llvm_ir_for_asan(ll_path.read_text(encoding="utf-8")), encoding="utf-8")
        compile_ll_path = san_ll_path

    if linker == clang_bin:
        subprocess.run(
            [clang_bin, "-O1", "-g", "-Wno-override-module", *extra_inc, *san_flags, str(compile_ll_path), str(driver_c_path), "-o", str(out_bin_path)],
            check=True,
            capture_output=True,
            text=True,
        )
    else:
        obj_path = ll_path.with_suffix(".san.o")
        subprocess.run(
            [clang_bin, "-O1", "-g", "-Wno-override-module", *extra_inc, *san_flags, "-c", str(compile_ll_path), "-o", str(obj_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            [linker, "-O1", "-g", *san_flags, str(obj_path), str(driver_c_path), "-o", str(out_bin_path)],
            check=True,
            capture_output=True,
            text=True,
        )
    return {
        "asan": asan,
        "ubsan": ubsan,
        "ubsan_scope": "c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled",
        "compiled_llvm_ir_sha256": sha256_bytes(compile_ll_path.read_bytes()),
        "compiler": clang_bin,
        "linker": linker,
    }


def probe_engines(
    override_lean: str | None = None,
    override_core: str | None = None,
    override_clang: str | None = None,
    asan: bool | None = None,
    ubsan: bool | None = None,
) -> dict[str, Any]:
    if asan is None:
        asan = os.environ.get("TURBO_CONFORMANCE_ASAN") == "1"
    if ubsan is None:
        ubsan = os.environ.get("TURBO_CONFORMANCE_UBSAN") == "1"
    lean_bin = override_lean if override_lean is not None else find_lean_binary()
    core_bin = override_core if override_core is not None else str(LEAN_NATIVE_CORE)
    full_bin = str(LEAN_NATIVE_FULL) if LEAN_NATIVE_FULL.is_file() else None
    clang_bin = override_clang if override_clang is not None else find_clang_binary()
    lean_ok = bool(lean_bin and Path(lean_bin).is_file() and os.access(lean_bin, os.X_OK))
    core_ok = bool(core_bin and Path(core_bin).is_file() and os.access(core_bin, os.X_OK))
    full_ok = bool(full_bin and Path(full_bin).is_file() and os.access(full_bin, os.X_OK))
    clang_ok = bool(clang_bin and Path(clang_bin).is_file() and os.access(clang_bin, os.X_OK))
    extra_inc = clang_extra_flags(clang_bin) if clang_ok and clang_bin else []
    sanitizer_linker = (
        find_sanitizer_linker(clang_bin, extra_inc, asan, ubsan)
        if (asan or ubsan) and clang_ok
        else (clang_bin if clang_ok else None)
    )
    san_ok = bool(sanitizer_linker) if (asan or ubsan) else True
    if core_ok:
        try:
            subprocess.run([core_bin, "validate-tv", "--canonical-benchmark", "--json"],
                           check=True, capture_output=True, text=True)
        except (subprocess.CalledProcessError, OSError):
            core_ok = False
    return {
        "lean_bin": lean_bin if lean_ok else None,
        "core_bin": core_bin if core_ok else None,
        "full_bin": full_bin if full_ok else None,
        "clang_bin": clang_bin if clang_ok else None,
        "sanitizer_linker": sanitizer_linker,
        "sanitizers_ready": san_ok,
        "stock_lean_c": lean_ok and clang_ok,
        "lnir_eval": core_ok and full_ok,
        "c_abi_llvm": core_ok and full_ok and clang_ok and san_ok,
    }


def run_three_way_batch(
    programs: list[dict[str, Any]],
    engines: dict[str, Any],
    mutate_engine: str | None = None,
    asan: bool | None = None,
    ubsan: bool | None = None,
) -> dict[str, Any]:
    """Execute ALL fuzz programs through:
      (1) stock `lean -c` + `clang` binary execution,
      (2) frontend lowering (`lean-native emit-lnir --wire`) + `lean-native-core eval-lnir --batch-json --opt` + `validate-tv`,
      (3) `lean-native-core compile-llvm` + `clang` binary execution.
    """
    if asan is None:
        asan = os.environ.get("TURBO_CONFORMANCE_ASAN") == "1"
    if ubsan is None:
        ubsan = os.environ.get("TURBO_CONFORMANCE_UBSAN") == "1"
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
        seen_preambles: list[str] = []
        for p in programs:
            pre = p.get("preamble", "")
            if pre and pre not in seen_preambles:
                seen_preambles.append(pre)
                lean_lines.append(pre)
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
            [core_bin, "compile-llvm", "--no-telemetry", "--lnir", str(wire_path), "-o", str(ll_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        san_meta = compile_and_link_llvm_driver(
            clang_bin=clang_bin,
            extra_inc=extra_inc,
            ll_path=ll_path,
            driver_c_path=driver_c_path,
            out_bin_path=ln_bin_path,
            asan=asan,
            ubsan=ubsan,
            sanitizer_linker=engines.get("sanitizer_linker"),
        )
        run_env = dict(os.environ)
        if asan:
            run_env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=1:halt_on_error=1"
        if ubsan:
            run_env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
        ln_out = subprocess.run([str(ln_bin_path)], env=run_env, check=True, capture_output=True, text=True).stdout
        ln_vals = [int(x) for x in json.loads(ln_out)]
        if len(stock_vals) != len(programs) or len(ln_vals) != len(programs):
            raise RuntimeError("Native execution skipped or duplicated rows")
        if mutate_engine == "c_abi_llvm" and ln_vals:
            ln_vals[-1] = u64(ln_vals[-1] ^ 0xDEAD)

        mismatches = []
        wire_tokens = wire_path.read_text().strip().split("|")
        lowered_decls = [bytes.fromhex(wire_tokens[i + 1]).decode("utf-8")
                         for i, token in enumerate(wire_tokens) if token == "D_decl"]
        if len(lowered_decls) != len(set(lowered_decls)) or not expected_decls <= set(lowered_decls):
            raise RuntimeError("Lowered module skipped or duplicated requested declarations")
        validate_tv_coverage(tv_json, set(lowered_decls))
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

        raw_ir_sha = sha256_bytes(ll_path.read_bytes())
        if san_meta.get("asan") is not bool(asan) or san_meta.get("ubsan") is not bool(ubsan):
            raise RuntimeError("Sanitizer execution receipt did not match requested sanitizer flags")
        if asan and san_meta.get("compiled_llvm_ir_sha256") == raw_ir_sha:
            if "sanitize_address" not in ll_path.read_text(encoding="utf-8"):
                raise RuntimeError("ASan requested but compiled LLVM IR hash matched uninstrumented IR")
        receipts = {
            "lean_source_sha256": sha256_bytes(lean_file.read_bytes()),
            "stock_source_sha256": sha256_bytes(stock_source.read_bytes()),
            "stock_unmodified_c_sha256": sha256_bytes(lean_c_file.read_bytes()),
            "stock_runtime": "stock lean -c + leanc (full generated C, no replacements)",
            "lnir_wire_sha256": sha256_bytes(wire_path.read_bytes()),
            "llvm_ir_sha256": raw_ir_sha,
            "compiled_llvm_ir_sha256": san_meta["compiled_llvm_ir_sha256"],
            "stock_binary_sha256": sha256_bytes(stock_bin_path.read_bytes()),
            "leannative_binary_sha256": sha256_bytes(ln_bin_path.read_bytes()),
            "sanitizers": san_meta,
            "symbolic_tv_passed_decls": tv_json.get("passedDecls", 0),
            "lnir_eval_executed_decls": len(ev_by_decl),
        }
        return {
            "executed_count": len(programs),
            "mismatches": mismatches,
            "live_objects": total_live_objs,
            "receipts": receipts,
        }


def alias_program_to_lean_lines(program: dict[str, Any]) -> list[str]:
    """Emit the three exported decls of one alias program (ret, old_read, new_read).

    All three recompute the same aliasing sequence so every observable is a live
    function of the shared/exclusive reuse decision the lowering must get right.
    """
    seed = program["seed"]
    probe = program["alias_probe"]
    idx = u64(probe["idx"])
    jdx = u64(probe["jdx"])
    val = u64(probe["val"])
    c1 = u64(probe["c1"])
    c2 = u64(probe["c2"])
    init = f"FuzzPacket.pkt (x0, x0 ^^^ ({c1} : UInt64)) (x0 + ({c2} : UInt64), x0 * ({3} : UInt64))"
    alias = "base" if program["alias_shared"] else (
        f"FuzzPacket.pkt (x0 ^^^ ({11} : UInt64), x0 + ({13} : UInt64)) (x0 * ({17} : UInt64), x0 + ({19} : UInt64))"
    )
    prologue = (
        f"  let base := {init}\n"
        f"  let alias := {alias}\n"
        f"  let stepped := fuzzPacketStep alias (x0 + ({val} : UInt64))\n"
    )
    ret_body = (
        prologue
        + "  let direct := fuzzPacketFold base\n"
        + "  let canary := fuzzPacketFold base\n"
        + f"  let after := fuzzPacketStep base (x0 ^^^ ({val} : UInt64))\n"
        + f"  (direct + fuzzP1 stepped + canary) ^^^ (fuzzPacketFold after + ({jdx} : UInt64))"
    )
    old_body = prologue + f"  fuzzPacketFold base + fuzzP2 stepped ^^^ ({idx} : UInt64)"
    new_body = (
        prologue
        + f"  let after := fuzzPacketStep base (x0 ^^^ ({val} : UInt64))\n"
        + f"  (fuzzPacketFold stepped + fuzzPacketFold after) ^^^ (fuzzQ2 base + ({idx} : UInt64))"
    )
    return [
        f"@[export fuzz_seed_{seed}]",
        f"def fuzz_seed_{seed} (x0 : UInt64) : UInt64 :=",
        ret_body,
        "",
        f"@[export fuzz_seed_{seed}_old]",
        f"def fuzz_seed_{seed}_old (x0 : UInt64) : UInt64 :=",
        old_body,
        "",
        f"@[export fuzz_seed_{seed}_new]",
        f"def fuzz_seed_{seed}_new (x0 : UInt64) : UInt64 :=",
        new_body,
        "",
    ]


def alias_decl_names(program: dict[str, Any]) -> list[str]:
    seed = program["seed"]
    return [f"fuzz_seed_{seed}", f"fuzz_seed_{seed}_old", f"fuzz_seed_{seed}_new"]


def run_alias_batch(
    programs: list[dict[str, Any]],
    engines: dict[str, Any],
    mutate_engine: str | None = None,
    asan: bool = False,
    ubsan: bool = False,
) -> dict[str, Any]:
    """Execute alias programs two-way (stock Lean C vs LNIR interpreter) with validate-tv.

    compile-llvm of heap decls must fail closed (documented Stage 1D behavior);
    if a future backend accepts the wire, the batch upgrades to three-way.
    """
    lean_bin = engines["lean_bin"]
    core_bin = engines["core_bin"]
    full_bin = engines.get("full_bin")
    if not full_bin:
        raise RuntimeError("Missing real Lean frontend; core is not a substitute")
    if not programs:
        return {
            "executed_count": 0,
            "mismatches": [],
            "live_objects": 0,
            "leaks": 0,
            "alias_llvm_fail_closed": True,
            "alias_llvm_refusal": "no programs",
            "receipts": [],
        }

    with tempfile.TemporaryDirectory(prefix="turbo_c4_alias_batch_") as tmp:
        tmpdir = Path(tmp)
        lean_lines = ["-- Auto-generated Tier C4 alias batch (C4x)"]
        lean_lines.append(ALIAS_PREAMBLE)
        c_driver_decls = ["#include <stdint.h>", "#include <stdio.h>"]
        c_driver_calls = ["int main(void) {", '  printf("[");']
        arg_list_strs: list[str] = []
        decl_order: list[tuple[str, int]] = []
        for p in programs:
            lean_lines.extend(alias_program_to_lean_lines(p))
            arg0 = u64(p["arg0"])
            for decl in alias_decl_names(p):
                c_driver_decls.append(f"extern uint64_t {decl}(uint64_t);")
                sep = "," if decl_order else ""
                c_driver_calls.append(
                    f'  printf("{sep}\\"%llu\\"", (unsigned long long){decl}({arg0}ULL));'
                )
                arg_list_strs.append(f"{decl}:{arg0}")
                decl_order.append((decl, p["seed"]))
        c_driver_calls.append('  printf("]\\n");')
        c_driver_calls.append("  return 0;")
        c_driver_calls.append("}")

        lean_src = "\n".join(lean_lines) + "\n"
        lean_file = tmpdir / "AliasBatch.lean"
        lean_file.write_text(lean_src, encoding="utf-8")

        stock_source = tmpdir / "StockAlias.lean"
        stock_calls = [
            f"toString ({decl} {u64(p['arg0'])})"
            for p in programs
            for decl in alias_decl_names(p)
        ]
        stock_source.write_text(
            lean_src + '\ndef main : IO Unit :=\n  IO.println ("[" ++ String.intercalate "," ['
            + ", ".join(stock_calls) + '] ++ "]")\n', encoding="utf-8"
        )
        lean_c_file = tmpdir / "AliasBatch.lean.c"
        subprocess.run(
            [lean_bin, str(stock_source), "-c", str(lean_c_file)],
            cwd=str(tmpdir), check=True, capture_output=True, text=True,
        )
        driver_c_path = tmpdir / "alias_driver.c"
        stock_bin_path = tmpdir / "stock_alias_runner"
        driver_c_path.write_text(
            "\n".join(c_driver_decls) + "\n" + "\n".join(c_driver_calls) + "\n",
            encoding="utf-8",
        )
        lean_prefix = subprocess.run([lean_bin, "--print-prefix"], check=True, capture_output=True, text=True).stdout.strip()
        leanc = str(Path(lean_prefix) / "bin" / "leanc")
        subprocess.run(
            [leanc, "-O2", str(lean_c_file), "-o", str(stock_bin_path)],
            check=True, capture_output=True, text=True,
        )
        stock_out = subprocess.run([str(stock_bin_path)], check=True, capture_output=True, text=True).stdout
        stock_flat = [int(x) for x in json.loads(stock_out)]
        if len(stock_flat) != len(decl_order):
            raise RuntimeError("Stock alias execution skipped or duplicated rows")
        stock_obs = [
            {"ret": stock_flat[i], "old_read": stock_flat[i + 1], "new_read": stock_flat[i + 2]}
            for i in range(0, len(stock_flat), 3)
        ]
        if mutate_engine == "stock_lean_c" and stock_obs:
            stock_obs[0]["ret"] = u64(stock_obs[0]["ret"] ^ 1)

        wire_path = tmpdir / "alias_batch.lnir"
        subprocess.run(
            [full_bin, "emit-lnir", "--wire", "--allow-rc-adt", str(lean_file), "-o", str(wire_path)],
            check=True, capture_output=True, text=True,
        )
        tv_out = subprocess.run(
            [core_bin, "validate-tv", "--lnir", str(wire_path), "--json"],
            check=True, capture_output=True, text=True,
        ).stdout
        tv_json = json.loads(tv_out)
        ev_res = subprocess.run(
            [core_bin, "eval-lnir", "--lnir", str(wire_path), "--args", ";".join(arg_list_strs),
             "--opt", "--batch-json"],
            check=True, capture_output=True, text=True,
        )
        ev_rows = json.loads(ev_res.stdout)
        expected_decls = {decl for decl, _ in decl_order}
        if len(ev_rows) != len(decl_order) or any(r.get("ok") is not True for r in ev_rows) \
                or {r.get("decl") for r in ev_rows} != expected_decls:
            raise RuntimeError("Alias evaluation did not execute each exact requested declaration once")
        ev_by_decl = {r["decl"]: r for r in ev_rows}
        leaked_rows = [r for r in ev_rows if int(r.get("live_objects", 0)) != 0]
        lnir_flat = {}
        for decl, _seed in decl_order:
            row = ev_by_decl[decl]
            lnir_flat[decl] = int(row["value_u64"])
        lnir_obs = []
        for p in programs:
            names = alias_decl_names(p)
            lnir_obs.append({
                "ret": lnir_flat[names[0]],
                "old_read": lnir_flat[names[1]],
                "new_read": lnir_flat[names[2]],
            })
        if mutate_engine == "lnir_eval" and lnir_obs:
            lnir_obs[-1]["new_read"] = u64(lnir_obs[-1]["new_read"] ^ 1)

        llvm_res = subprocess.run(
            [core_bin, "compile-llvm", "--no-telemetry", "--lnir", str(wire_path), "-o", str(tmpdir / "alias_batch.ll")],
            capture_output=True, text=True,
        )
        llvm_obs: list[dict[str, Any]] | None = None
        alias_llvm_fail_closed = True
        alias_llvm_refusal = ""
        if llvm_res.returncode != 0:
            alias_llvm_refusal = (llvm_res.stderr or llvm_res.stdout).strip().splitlines()[0][:200] if (llvm_res.stderr or llvm_res.stdout).strip() else "unknown refusal"
        else:
            alias_llvm_fail_closed = False
            ll_path = tmpdir / "alias_batch.ll"
            ln_bin_path = tmpdir / "ln_alias_runner"
            driver_c_path.write_text(
                "\n".join(c_driver_decls) + "\n" + "\n".join(c_driver_calls) + "\n",
                encoding="utf-8",
            )
            san_meta = compile_and_link_llvm_driver(
                clang_bin=engines["clang_bin"],
                extra_inc=clang_extra_flags(engines["clang_bin"]),
                ll_path=ll_path,
                driver_c_path=driver_c_path,
                out_bin_path=ln_bin_path,
                asan=asan,
                ubsan=ubsan,
                sanitizer_linker=engines.get("sanitizer_linker"),
            )
            run_env = dict(os.environ)
            if asan:
                run_env["ASAN_OPTIONS"] = "detect_leaks=0:abort_on_error=1:halt_on_error=1"
            if ubsan:
                run_env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
            ln_out = subprocess.run([str(ln_bin_path)], env=run_env, check=True, capture_output=True, text=True).stdout
            ln_flat = [int(x) for x in json.loads(ln_out)]
            if len(ln_flat) != len(decl_order):
                raise RuntimeError("LLVM alias execution skipped or duplicated rows")
            llvm_obs = [
                {"ret": ln_flat[i], "old_read": ln_flat[i + 1], "new_read": ln_flat[i + 2]}
                for i in range(0, len(ln_flat), 3)
            ]
            if mutate_engine == "c_abi_llvm" and llvm_obs:
                llvm_obs[-1]["ret"] = u64(llvm_obs[-1]["ret"] ^ 0xDEAD)
            san_receipt = {"sanitizers": san_meta, "compiled_llvm_ir_sha256": sha256_bytes(ll_path.read_bytes())}

        mismatches = []
        for p_i, (p, so, lo) in enumerate(zip(programs, stock_obs, lnir_obs)):
            vo = llvm_obs[p_i] if llvm_obs is not None else None
            m = alias_mismatch(p, so, lo, vo)
            if m is not None:
                mismatches.append(m)

        receipts = [{
            "lean_source_sha256": sha256_bytes(lean_file.read_bytes()),
            "lnir_wire_sha256": sha256_bytes(wire_path.read_bytes()),
            "stock_binary_sha256": sha256_bytes(stock_bin_path.read_bytes()),
            "symbolic_tv_passed_decls": tv_json.get("passedDecls", 0),
            "lnir_eval_executed_decls": len(ev_by_decl),
            "alias_llvm_fail_closed": alias_llvm_fail_closed,
            "alias_llvm_refusal": alias_llvm_refusal,
        }]
        if alias_llvm_fail_closed is False:
            receipts[0].update(san_receipt)
        return {
            "executed_count": len(programs),
            "mismatches": mismatches,
            "live_objects": sum(int(r.get("live_objects", 0)) for r in ev_rows),
            "leaks": len(leaked_rows),
            "alias_llvm_fail_closed": alias_llvm_fail_closed,
            "alias_llvm_refusal": alias_llvm_refusal,
            "receipts": receipts,
        }


def validate_tv_coverage(report: Any, expected_decls: set[str]) -> None:
    """A successful summary cannot replace executed, named validation obligations."""
    count = len(expected_decls)
    if not count or not isinstance(report, dict) or report.get("allPassed") is not True:
        raise RuntimeError("Translation validation failed or returned an invalid report")
    if report.get("schemaVersion") != "lean-native-symbolic-tv-v2":
        raise RuntimeError("Translation validation failed or returned an invalid report")
    if any(type(report.get(k)) is not int or report[k] != count
           for k in ("passedDecls", "totalDecls")):
        raise RuntimeError("Translation validation skipped or duplicated declarations")
    rows = report.get("declResults")
    if (not isinstance(rows, list) or len(rows) != count
            or any(not isinstance(r, dict) or not isinstance(r.get("declName"), str)
                   or any(r.get(key) is not True for key in
                          ("passed", "ubRefines", "domainEquiv", "poisonRefines", "symRetEquiv",
                           "concreteRefines", "memWritesEquiv"))
                   or any(not isinstance(r.get(key), str) or not r[key] for key in ("srcHash", "tgtHash"))
                   or type(r.get("concreteSamplesTot")) is not int or r["concreteSamplesTot"] <= 0
                   or type(r.get("concreteSamplesOk")) is not int
                   or r["concreteSamplesOk"] != r["concreteSamplesTot"] for r in rows)
            or {r["declName"] for r in rows} != expected_decls):
        raise RuntimeError("Translation validation lacks exact successful declaration coverage")


SCALAR_CHUNK = 256
ALIAS_CHUNK = 96


def _chunk(items: list[Any], size: int) -> list[list[Any]]:
    return [items[i:i + size] for i in range(0, len(items), size)] if items else []


def merge_fuzz_receipts(scalar_receipts: list[dict[str, Any]], alias_receipts: list[dict[str, Any]]) -> dict[str, Any]:
    """Aggregate per-batch receipts into the historical single-dict shape.

    P0 callers (test_p0_trust_boundary.py) read run_fuzzer()["receipts"] as a
    dict, so executed/passing declaration counts are summed across batches, the
    first scalar batch's digests keep their historical top-level keys, and the
    full per-batch detail stays available under `batch_receipts`.
    """
    all_batches = list(scalar_receipts) + list(alias_receipts)
    first_scalar = next((r for r in scalar_receipts if r), {})
    last_scalar = next((r for r in reversed(scalar_receipts) if r), {})
    merged: dict[str, Any] = dict(first_scalar)
    merged["scalar_batch_count"] = len(scalar_receipts)
    merged["alias_batch_count"] = len(alias_receipts)
    for key in ("lnir_eval_executed_decls", "symbolic_tv_passed_decls"):
        merged[key] = sum(int(r.get(key, 0) or 0) for r in all_batches)
    merged["stock_runtime"] = last_scalar.get(
        "stock_runtime", "stock lean -c + leanc (full generated C, no replacements)"
    )
    merged["batch_receipts"] = all_batches
    return merged


def run_fuzzer(
    num_seeds: int = 50,
    override_lean: str | None = None,
    override_core: str | None = None,
    override_clang: str | None = None,
    mutate_engine: str | None = None,
    asan: bool = False,
    ubsan: bool = False,
) -> dict[str, Any]:
    n = max(0, num_seeds)
    programs = [build_program(seed) for seed in range(n)]
    alias_programs = [p for p in programs if program_contains_alias(p)]
    scalar_programs = [p for p in programs if not program_contains_alias(p)]
    alias_floor = n // ALIAS_FLOOR_RATIO
    alias_counts = {
        "alias_program_count": len(alias_programs),
        "alias_shared_count": sum(1 for p in alias_programs if p["alias_shared"]),
        "alias_exclusive_count": sum(1 for p in alias_programs if not p["alias_shared"]),
        "alias_floor": alias_floor,
        "alias_floor_met": len(alias_programs) >= alias_floor,
    }
    engines = probe_engines(override_lean, override_core, override_clang, asan=asan, ubsan=ubsan)
    all_engines_ready = (
        engines["stock_lean_c"] and engines["lnir_eval"] and engines["c_abi_llvm"]
    )
    if not all_engines_ready:
        return {
            "schemaVersion": "turbo-lean-lcnf-fuzz-v3",
            "tier": "C4",
            "status": "incomplete_missing_engine",
            "ok": False,
            "seeds": n,
            "checked": 0,
            "mismatch_count": 0,
                "rc_leak_count": None,
                "asan": asan,
                "ubsan": ubsan,
                "ubsan_scope": "c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled",
                "coverage": "scalar_3way_plus_alias_2way_seqfor_unrolled",
                **alias_counts,
            "parity": "incomplete",
            "engines": {
                "stock_lean_c": engines["stock_lean_c"],
                "lnir_validate_tv": engines["lnir_eval"],
                "c_abi_llvm": engines["c_abi_llvm"],
            },
            "boundary_scalars": list(BOUNDARY_SCALARS),
            "shrunk_failures": [{"error": "Required conformance engines unavailable; refusing to report pass"}],
        }

    mismatches = 0
    failures: list[dict[str, Any]] = []
    scalar_receipts: list[dict[str, Any]] = []
    alias_receipts: list[dict[str, Any]] = []
    checked = 0
    scalar_live_objects = 0
    alias_checked = 0
    alias_leaks = 0
    alias_live_objects = 0
    alias_llvm_all_fail_closed = True
    alias_refusals: list[str] = []
    scalar_batches = _chunk(scalar_programs, SCALAR_CHUNK)
    alias_batches = _chunk(alias_programs, ALIAS_CHUNK)

    for b_idx, batch in enumerate(scalar_batches):
        batch_mutate = mutate_engine if (
            (mutate_engine == "stock_lean_c" and b_idx == 0)
            or (mutate_engine in ("lnir_eval", "c_abi_llvm") and b_idx == len(scalar_batches) - 1)
        ) else None
        try:
            batch_res = run_three_way_batch(batch, engines, mutate_engine=batch_mutate, asan=asan, ubsan=ubsan)
        except (subprocess.SubprocessError, OSError, ValueError, RuntimeError) as exc:
            batch_res = {"executed_count": 0, "mismatches": [], "receipts": {}}
            failures.append({"error": str(exc), "stderr": getattr(exc, "stderr", None), "stage": "scalar_batch", "index": b_idx})
        mismatches += len(batch_res["mismatches"])
        failures.extend(batch_res["mismatches"])
        checked += batch_res["executed_count"]
        scalar_live_objects += batch_res.get("live_objects", 0) or 0
        if isinstance(batch_res.get("receipts"), dict):
            scalar_receipts.append(batch_res["receipts"])

    for b_idx, batch in enumerate(alias_batches):
        batch_mutate = mutate_engine if (
            (mutate_engine == "stock_lean_c" and b_idx == 0)
            or (mutate_engine in ("lnir_eval", "c_abi_llvm") and b_idx == len(alias_batches) - 1)
        ) else None
        try:
            batch_res = run_alias_batch(batch, engines, mutate_engine=batch_mutate, asan=asan, ubsan=ubsan)
        except (subprocess.SubprocessError, OSError, ValueError, RuntimeError) as exc:
            batch_res = {"executed_count": 0, "mismatches": [], "receipts": [], "leaks": 0,
                         "live_objects": 0, "alias_llvm_fail_closed": True, "alias_llvm_refusal": str(exc)}
            failures.append({"error": str(exc), "stderr": getattr(exc, "stderr", None), "stage": "alias_batch", "index": b_idx})
        mismatches += len(batch_res["mismatches"])
        failures.extend(batch_res["mismatches"])
        checked += batch_res["executed_count"]
        alias_checked += batch_res["executed_count"]
        alias_leaks += batch_res.get("leaks", 0)
        alias_live_objects += batch_res.get("live_objects", 0)
        alias_llvm_all_fail_closed = alias_llvm_all_fail_closed and bool(batch_res.get("alias_llvm_fail_closed"))
        if batch_res.get("alias_llvm_refusal"):
            alias_refusals.append(str(batch_res["alias_llvm_refusal"]))
        alias_receipts.extend(batch_res.get("receipts", []))

    receipts = merge_fuzz_receipts(scalar_receipts, alias_receipts)

    rc_leak_count = alias_leaks if alias_checked > 0 else None
    alias_coverage_ok = alias_counts["alias_floor_met"] and (alias_checked == 0 or (alias_leaks == 0 and alias_checked == len(alias_programs)))
    parity_ok = n > 0 and checked == n and mismatches == 0 and not failures and alias_coverage_ok
    return {
        "schemaVersion": "turbo-lean-lcnf-fuzz-v3",
        "tier": "C4",
        "status": ("passed_scalar_plus_alias" if parity_ok and alias_checked > 0
                   else "passed_scalar_only" if parity_ok else "failed_or_incomplete"),
        "coverage": "scalar_3way_plus_alias_2way_seqfor_unrolled",
        "ok": parity_ok,
        "seeds": n,
        "checked": checked,
        "mismatch_count": mismatches,
        "rc_leak_count": rc_leak_count,
        "asan": asan,
        "ubsan": ubsan,
        "ubsan_scope": "c_driver_and_link_runtime_only_not_llvm_ir" if ubsan else "disabled",
        "interpreter_live_objects": scalar_live_objects,
        "alias_live_objects": alias_live_objects,
        **alias_counts,
        "alias_checked": alias_checked,
        "alias_llvm_fail_closed": alias_llvm_all_fail_closed,
        "alias_llvm_refusals": alias_refusals[:4],
        "parity": "100%" if (parity_ok and n > 0) else f"{checked - mismatches}/{checked}",
        "engines": {
            "stock_lean_c": engines["stock_lean_c"],
            "lnir_validate_tv": engines["lnir_eval"],
            "c_abi_llvm": engines["c_abi_llvm"],
        },
        "receipts": receipts,
        "boundary_scalars": list(BOUNDARY_SCALARS),
        "shrunk_failures": failures[:8],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Tier C4 LCNF/LNIR differential fuzzer")
    ap.add_argument("--seeds", type=int, default=64, help="Number of deterministic seeds")
    ap.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    ap.add_argument("--mutate-engine", type=str, default=None, help="Inject mutation into stock_lean_c|lnir_eval|c_abi_llvm")
    ap.add_argument("--asan", action="store_true", help="Instrument compiled LLVM IR + C driver with AddressSanitizer")
    ap.add_argument(
        "--ubsan",
        action="store_true",
        help="Instrument C driver and link runtime with UndefinedBehaviorSanitizer (pre-emitted LLVM IR is not UBSan-instrumented)",
    )
    args = ap.parse_args()
    report = run_fuzzer(args.seeds, mutate_engine=args.mutate_engine, asan=args.asan, ubsan=args.ubsan)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        status = "PASSED" if report["ok"] else f"FAILED ({report['status']})"
        print(
            f"[fuzz-lcnf] {status} seeds={report['seeds']} checked={report['checked']} "
            f"mismatches={report['mismatch_count']} rc_leaks={report['rc_leak_count']} "
            f"alias={report['alias_program_count']}"
            f"({report['alias_shared_count']}s/{report['alias_exclusive_count']}x,"
            f"floor={'met' if report['alias_floor_met'] else 'MISSED'}) "
            f"stock_lean={report['engines']['stock_lean_c']} "
            f"tv={report['engines']['lnir_validate_tv']} "
            f"clang={report['engines']['c_abi_llvm']}"
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
