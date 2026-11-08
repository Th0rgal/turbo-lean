#!/usr/bin/env python3
"""Zero-Lean-build offline conformance validator for `turbo-lean` external plugins.

Validates any JSONL-stdio plugin executable (default: `sdk/accelerator-template/plugin.py`)
against the exact Rust (`ExternalProcessAccelerator` in `crates/turbo-lean/src/accelerators.rs`)
and Lean (`runExternalOptPlugin` / `verifyOptPluginGate` in `lean/LeanNative/Transform/Plugins.lean`)
protocol contracts in under 1 second using Python 3 standard library only:

1. `accelerators.example.json` schema validation (`AcceleratorConfig` / `ExternalAcceleratorSpec`).
2. Tactic `AcceleratorInput` -> `AcceleratorCertificate` roundtrip (`rewritten_proof`,
   `counterexample_found`, `subgoal_cuts`, and `{}` abstention).
3. `LNIR_WIRE_V1|` optimization roundtrip, signature preservation, 64-state boundary + SplitMix64
   concrete `evalCode` equivalence, and target scalar cycle-cost non-increase (`costAfter <= costBefore`).
4. Malformed / adversarial JSONL & wire input resilience (clean `{}` abstention, zero crashes).
5. Subprocess timeout & hard-kill fault isolation (`budget_ms` enforcement).
"""
import argparse
import json
import re
import shlex
import subprocess
import sys
import time
import unittest
from dataclasses import dataclass
from pathlib import Path

SDK_DIR = Path(__file__).resolve().parent
FIXTURES_DIR = SDK_DIR / "fixtures"
DEFAULT_PLUGIN = SDK_DIR / "plugin.py"
MASK64 = (1 << 64) - 1
MASK256 = (1 << 256) - 1
Val = tuple[str, object]

BOUNDARY_U64 = (
    0, 1, 2, 3, 7, 15, 31, 32, 63, 64,
    (1 << 31) - 1, 1 << 31, (1 << 32) - 1, 1 << 32,
    (1 << 63) - 1, 1 << 63, MASK64 - 1, MASK64,
)

BOUNDARY_U256 = (
    0,
    1,
    0xFFFFFFFFFFFFFFFF,
    (1 << 128) - 1,
    1 << 255,
    MASK256,
)

BOUNDARY_U256_PAIRS = (
    (0, 0),
    (1, 0),
    (MASK256, 1),
    (0, 1),
    (1 << 255, 2),
    (0xFFFFFFFFFFFFFFFF, (1 << 128) - 1),
    (1, 1),
    (MASK256, MASK256),
)


class EvalUBError(Exception):
    """Runtime undefined behavior matching `LeanNative.Semantics.UBError` (not a structural AST/type bug)."""

TARGET_COST_PROFILES: dict[str, dict[str, int]] = {
    "x86_64": {
        "addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 4, "divMod": 24,
        "fma": 3, "select": 2, "clz256": 2, "addSubChecked256": 3, "mulChecked256": 4,
    },
    "arm64": {
        "addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 4, "divMod": 24,
        "fma": 2, "select": 2, "clz256": 2, "addSubChecked256": 3, "mulChecked256": 4,
    },
    "cuda_ptx": {
        "addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 5, "divMod": 36,
        "fma": 2, "select": 2, "clz256": 2, "addSubChecked256": 3, "mulChecked256": 5,
    },
    "apple_metal": {
        "addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 5, "divMod": 36,
        "fma": 2, "select": 2, "clz256": 2, "addSubChecked256": 3, "mulChecked256": 5,
    },
}


def splitmix64(x: int) -> int:
    z = (x + 0x9E3779B97F4A7C15) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return (z ^ (z >> 31)) & MASK64


def validate_accelerator_config_dict(cfg: object) -> None:
    if not isinstance(cfg, dict):
        raise ValueError("AcceleratorConfig must be a JSON object")
    allowed_top = {"enabled", "default_budget_ms", "disabled_builtins", "external"}
    unknown_top = set(cfg) - allowed_top
    if unknown_top:
        raise ValueError(f"Unknown AcceleratorConfig keys: {sorted(unknown_top)}")
    if not isinstance(cfg.get("enabled", True), bool):
        raise ValueError("`enabled` must be a bool")
    budget = cfg.get("default_budget_ms", 25)
    if not isinstance(budget, int) or isinstance(budget, bool) or budget < 1:
        raise ValueError("`default_budget_ms` must be a positive integer")
    dis = cfg.get("disabled_builtins", [])
    if not isinstance(dis, list) or not all(isinstance(x, str) for x in dis):
        raise ValueError("`disabled_builtins` must be a list of strings")
    ext = cfg.get("external", [])
    if not isinstance(ext, list):
        raise ValueError("`external` must be a list of ExternalAcceleratorSpec objects")
    for spec in ext:
        if not isinstance(spec, dict):
            raise ValueError("ExternalAcceleratorSpec must be an object")
        allowed_spec = {"name", "command", "timeout_ms", "trigger_tactics"}
        unknown_spec = set(spec) - allowed_spec
        if unknown_spec:
            raise ValueError(f"Unknown ExternalAcceleratorSpec keys: {sorted(unknown_spec)}")
        if not isinstance(spec.get("name"), str) or not spec["name"].strip():
            raise ValueError("ExternalAcceleratorSpec.name must be a non-empty string")
        cmd = spec.get("command")
        if not isinstance(cmd, list) or not cmd or not all(isinstance(c, str) and c for c in cmd):
            raise ValueError("ExternalAcceleratorSpec.command must be a non-empty string list")
        t_ms = spec.get("timeout_ms", 25)
        if not isinstance(t_ms, int) or isinstance(t_ms, bool) or t_ms < 1:
            raise ValueError("ExternalAcceleratorSpec.timeout_ms must be a positive integer")
        trig = spec.get("trigger_tactics", [])
        if not isinstance(trig, list) or not all(isinstance(t, str) for t in trig):
            raise ValueError("ExternalAcceleratorSpec.trigger_tactics must be a string list")


def validate_tactic_certificate(raw_line: str) -> dict | None:
    trimmed = raw_line.strip()
    if trimmed in ("", "null", "{}"):
        return None
    obj = json.loads(trimmed)
    if obj is None or obj == {}:
        return None
    if not isinstance(obj, dict) or "kind" not in obj:
        raise ValueError(f"Certificate must be an object with tag `kind`, got: {obj!r}")
    kind = obj["kind"]
    if kind == "rewritten_proof":
        req = {"kind", "new_body_src", "accelerator_name", "estimated_speedup_hint"}
        if set(obj) != req:
            raise ValueError(f"rewritten_proof keys mismatch: {set(obj)} != {req}")
        for k in ("new_body_src", "accelerator_name", "estimated_speedup_hint"):
            if not isinstance(obj[k], str) or not obj[k].strip():
                raise ValueError(f"rewritten_proof.{k} must be a non-empty string")
    elif kind == "counterexample_found":
        allowed = {"kind", "witness_summary", "suggested_hypothesis", "accelerator_name"}
        if not {"kind", "witness_summary", "accelerator_name"}.issubset(obj) or not set(obj).issubset(allowed):
            raise ValueError(f"counterexample_found keys invalid: {set(obj)}")
        if not isinstance(obj["witness_summary"], str) or not obj["witness_summary"].strip():
            raise ValueError("counterexample_found.witness_summary must be non-empty")
        if not isinstance(obj["accelerator_name"], str) or not obj["accelerator_name"].strip():
            raise ValueError("counterexample_found.accelerator_name must be non-empty")
        sh = obj.get("suggested_hypothesis")
        if sh is not None and not isinstance(sh, str):
            raise ValueError("counterexample_found.suggested_hypothesis must be str or null")
    elif kind == "subgoal_cuts":
        req = {"kind", "cuts", "accelerator_name"}
        if set(obj) != req:
            raise ValueError(f"subgoal_cuts keys mismatch: {set(obj)} != {req}")
        cuts = obj["cuts"]
        if not isinstance(cuts, list) or len(cuts) < 2 or not all(isinstance(c, str) and c.strip() for c in cuts):
            raise ValueError("subgoal_cuts.cuts must be a list of >= 2 non-empty strings")
        if not isinstance(obj["accelerator_name"], str) or not obj["accelerator_name"].strip():
            raise ValueError("subgoal_cuts.accelerator_name must be non-empty")
    else:
        raise ValueError(f"Unknown AcceleratorCertificate kind: {kind!r}")
    return obj


@dataclass(frozen=True)
class ScalarAst:
    kind: str
    val: int | bool | str | None = None
    args: tuple["ScalarAst", ...] = ()


@dataclass(frozen=True)
class ParsedDecl:
    module_name: str
    name: str
    assurance: str
    is_gpu: bool
    params: list[tuple[int, str, bool, tuple[str, ...]]]
    ret_ty: tuple[str, ...]
    lets: list[tuple[int, tuple[str, ...], ScalarAst]]
    ret_var: int
    facts: tuple[tuple[str, ...], ...] = ()


class Cursor:
    def __init__(self, toks: list[str]) -> None:
        self.toks = toks
        self.i = 0

    def next(self) -> str:
        if self.i >= len(self.toks):
            raise ValueError("truncated LNIR_WIRE_V1 payload")
        t = self.toks[self.i]
        self.i += 1
        return t

    def next_nat(self) -> int:
        t = self.next()
        if not t.isdigit():
            raise ValueError(f"expected Nat token, got {t!r}")
        return int(t)

    def next_bool(self) -> bool:
        t = self.next()
        if t not in ("0", "1"):
            raise ValueError(f"expected Bool token, got {t!r}")
        return t == "1"

    def next_hex(self) -> str:
        t = self.next()
        if t == "_":
            return ""
        if len(t) % 2 != 0:
            raise ValueError(f"odd-length hex token: {t!r}")
        return bytes.fromhex(t).decode("utf-8")


def parse_type(cur: Cursor) -> tuple[str, ...]:
    t = cur.next()
    if t in ("T_i1", "T_i8", "T_i16", "T_i32", "T_i64", "T_usize", "T_u256", "T_i256",
             "T_f16", "T_f32", "T_f64", "T_objPtr", "T_taggedPtr", "T_storageMap", "T_unit"):
        return (t,)
    if t == "T_nat":
        return ("T_i64",)
    if t in ("T_sarray", "T_rawPtr"):
        return (t, *parse_type(cur))
    if t == "T_tuple":
        n = cur.next_nat()
        acc: list[str] = ["T_tuple", str(n)]
        for _ in range(n):
            acc.extend(parse_type(cur))
        return tuple(acc)
    raise ValueError(f"unknown LNIRType token: {t!r}")


def parse_scalar_ast(cur: Cursor) -> ScalarAst:
    tag = cur.next()
    if tag == "S_u64":
        return ScalarAst("u64", cur.next_nat() & MASK64)
    if tag == "S_bool":
        return ScalarAst("bool", cur.next_bool())
    if tag == "S_var":
        return ScalarAst("var", cur.next_nat())
    if tag == "S_bin":
        op = cur.next()
        return ScalarAst("bin", op, (parse_scalar_ast(cur), parse_scalar_ast(cur)))
    if tag == "S_un":
        op = cur.next()
        return ScalarAst("un", op, (parse_scalar_ast(cur),))
    if tag == "S_sel":
        return ScalarAst("sel", None, (parse_scalar_ast(cur), parse_scalar_ast(cur), parse_scalar_ast(cur)))
    if tag == "S_fma":
        return ScalarAst("fma", None, (parse_scalar_ast(cur), parse_scalar_ast(cur), parse_scalar_ast(cur)))
    raise ValueError(f"unsupported ScalarExpr tag: {tag!r}")


def parse_fact(cur: Cursor) -> tuple[str, ...]:
    tag = cur.next()
    if tag in ("F_lt", "F_aln"):
        return (tag, str(cur.next_nat()), str(cur.next_nat()))
    if tag in ("F_add", "F_sub", "F_mul"):
        a = str(cur.next_nat())
        b = str(cur.next_nat())
        nsw = "1" if cur.next_bool() else "0"
        nuw = "1" if cur.next_bool() else "0"
        return (tag, a, b, nsw, nuw)
    if tag == "F_disj":
        return (tag, str(cur.next_nat()), str(cur.next_nat()), str(cur.next_nat()), str(cur.next_nat()))
    if tag == "F_excl":
        return (tag, str(cur.next_nat()))
    raise ValueError(f"unknown RetainedFact tag: {tag!r}")


def parse_single_decl_wire(wire: str) -> ParsedDecl:
    cur = Cursor(wire.strip().split("|"))
    if cur.next() != "LNIR_WIRE_V1":
        raise ValueError("missing LNIR_WIRE_V1 header")
    mod_name = cur.next_hex()
    if cur.next_nat() != 1 or cur.next() != "D_decl":
        raise ValueError("expected single-declaration LNIRModule")
    name = cur.next_hex()
    assurance = cur.next()
    if assurance not in ("A_L0", "A_L1", "A_L2", "A_L3", "A_L4", "A_TEST"):
        raise ValueError(f"unknown AssuranceLevel token: {assurance!r}")
    is_gpu = cur.next_bool()
    plen = cur.next_nat()
    params: list[tuple[int, str, bool, tuple[str, ...]]] = []
    for _ in range(plen):
        pid = cur.next_nat()
        pname = cur.next_hex()
        pborrow = cur.next_bool()
        pty = parse_type(cur)
        params.append((pid, pname, pborrow, pty))
    ret_ty = parse_type(cur)
    lets: list[tuple[int, tuple[str, ...], ScalarAst]] = []
    while True:
        ctag = cur.next()
        if ctag == "C_ret":
            ret_var = cur.next_nat()
            break
        if ctag != "C_let":
            raise ValueError(f"unsupported LNIRCode tag in template validator: {ctag!r}")
        dst = cur.next_nat()
        ty = parse_type(cur)
        etag = cur.next()
        if etag != "E_scalar":
            raise ValueError(f"unsupported LNIRExpr tag in template validator: {etag!r}")
        lets.append((dst, ty, parse_scalar_ast(cur)))
    facts: list[tuple[str, ...]] = []
    if cur.i != len(cur.toks):
        if cur.next() != "F_facts":
            raise ValueError(f"unexpected trailing wire tokens: {cur.toks[cur.i - 1:]}")
        flen = cur.next_nat()
        for _ in range(flen):
            facts.append(parse_fact(cur))
    if cur.i != len(cur.toks):
        raise ValueError(f"unexpected trailing wire tokens after F_facts: {cur.toks[cur.i:]}")
    return ParsedDecl(mod_name, name, assurance, is_gpu, params, ret_ty, lets, ret_var, tuple(facts))


def clmul64(a: int, b: int) -> int:
    acc = 0
    for i in range(64):
        if ((b >> i) & 1) == 1:
            acc ^= (a << i) & MASK64
    return acc & MASK64


def clmul64_hi(a: int, b: int) -> int:
    acc = 0
    for i in range(1, 64):
        if ((b >> i) & 1) == 1:
            acc ^= (a >> (64 - i)) & MASK64
    return acc & MASK64


def gf2_affine(x: int, m: int) -> int:
    xb = x & 0xFF
    acc = 0
    for i in range(8):
        row = (m >> (i * 8)) & 0xFF
        dot = (row & xb).bit_count() & 1
        acc |= dot << i
    return acc


def eor3_u64(a: int, b: int) -> int:
    return (a ^ ((b >> 32) & 0xFFFFFFFF) ^ (b & 0xFFFFFFFF)) & MASK64


def to_u256(v: Val) -> int | None:
    if v[0] in ("u64", "u256"):
        return int(v[1]) & MASK256
    return None


def eval_bin_op(op: str, v1: Val, v2: Val) -> Val:
    t1, a = v1
    t2, b = v2
    if op == "B_add":
        if t1 == "u64" and t2 == "u64":
            return ("u64", (int(a) + int(b)) & MASK64)
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u64" and int(a) == 0:
            return v2
        if t1 == "u256" and t2 == "u256":
            return ("u256", (int(a) + int(b)) & MASK256)
    elif op == "B_sub":
        if t1 == "u64" and t2 == "u64":
            return ("u64", (int(a) - int(b)) & MASK64)
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u256" and t2 == "u256":
            return ("u256", (int(a) - int(b)) & MASK256)
    elif op == "B_mul":
        if t1 == "u64" and t2 == "u64":
            return ("u64", (int(a) * int(b)) & MASK64)
        if t2 == "u64" and int(b) == 1:
            return v1
        if t1 == "u64" and int(a) == 1:
            return v2
        if t1 == "u256" and t2 == "u256":
            return ("u256", (int(a) * int(b)) & MASK256)
    elif op == "B_div":
        if t1 == "u64" and t2 == "u64":
            return ("u64", 0 if int(b) == 0 else (int(a) // int(b)) & MASK64)
        if t2 == "u64" and int(b) == 1:
            return v1
        if t1 == "u256" and t2 == "u256":
            if int(b) == 0:
                raise EvalUBError("divisionByZero")
            return ("u256", (int(a) // int(b)) & MASK256)
    elif op == "B_mod":
        if t1 == "u64" and t2 == "u64":
            return ("u64", 0 if int(b) == 0 else (int(a) % int(b)) & MASK64)
        if t1 == "u256" and t2 == "u256":
            if int(b) == 0:
                raise EvalUBError("divisionByZero")
            return ("u256", (int(a) % int(b)) & MASK256)
    elif op == "B_bitAnd":
        if t1 == "u64" and t2 == "u64":
            return ("u64", int(a) & int(b))
        if t1 == "u256" and t2 == "u256":
            return ("u256", int(a) & int(b))
        if v1 == v2:
            return v1
    elif op == "B_bitOr":
        if t1 == "u64" and t2 == "u64":
            return ("u64", int(a) | int(b))
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u64" and int(a) == 0:
            return v2
        if t1 == "u256" and t2 == "u256":
            return ("u256", int(a) | int(b))
        if v1 == v2:
            return v1
    elif op == "B_bitXor":
        if t1 == "u64" and t2 == "u64":
            return ("u64", int(a) ^ int(b))
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u64" and int(a) == 0:
            return v2
        if t1 == "u256" and t2 == "u256":
            return ("u256", int(a) ^ int(b))
    elif op == "B_shl":
        if t1 == "u64" and t2 == "u64":
            return ("u64", (int(a) << (int(b) & 63)) & MASK64)
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u256" and t2 == "u256":
            sh = int(b)
            return ("u256", 0 if sh >= 256 else (int(a) << sh) & MASK256)
    elif op == "B_shr":
        if t1 == "u64" and t2 == "u64":
            return ("u64", (int(a) >> (int(b) & 63)) & MASK64)
        if t2 == "u64" and int(b) == 0:
            return v1
        if t1 == "u256" and t2 == "u256":
            sh = int(b)
            return ("u256", 0 if sh >= 256 else (int(a) >> sh) & MASK256)
    elif op == "B_sar":
        if t1 == "u64" and t2 == "u64":
            la = int(a) & MASK64
            sh = int(b) & 63
            shifted = la >> sh
            sign_bit = (la >> 63) & 1
            res = (shifted | ((MASK64 << (64 - sh)) & MASK64)) if (sign_bit != 0 and sh != 0) else shifted
            return ("u64", res & MASK64)
        if t1 == "u256" and t2 == "u256":
            la = int(a) & MASK256
            sh = int(b)
            is_neg = ((la >> 255) & 1) != 0
            if sh >= 256:
                return ("u256", MASK256 if is_neg else 0)
            if sh == 0:
                return ("u256", la)
            logical = la >> sh
            if not is_neg:
                return ("u256", logical)
            mask = (1 << 256) - (1 << (256 - sh))
            return ("u256", (logical | mask) & MASK256)
    elif op == "B_eq":
        if (t1 == "u64" and t2 == "u64") or (t1 == "u256" and t2 == "u256") or (t1 == "bool" and t2 == "bool"):
            return ("bool", a == b)
    elif op == "B_lt":
        if (t1 == "u64" and t2 == "u64") or (t1 == "u256" and t2 == "u256"):
            return ("bool", int(a) < int(b))
    elif op == "B_le":
        if (t1 == "u64" and t2 == "u64") or (t1 == "u256" and t2 == "u256"):
            return ("bool", int(a) <= int(b))
    elif op == "B_addChecked256":
        wa, wb = to_u256(v1), to_u256(v2)
        if wa is not None and wb is not None:
            if wa + wb > MASK256:
                raise EvalUBError("addChecked256 overflow")
            return ("u256", wa + wb)
    elif op == "B_subChecked256":
        wa, wb = to_u256(v1), to_u256(v2)
        if wa is not None and wb is not None:
            if wa < wb:
                raise EvalUBError("subChecked256 underflow")
            return ("u256", wa - wb)
    elif op == "B_mulChecked256":
        wa, wb = to_u256(v1), to_u256(v2)
        if wa is not None and wb is not None:
            if wa * wb > MASK256:
                raise EvalUBError("mulChecked256 overflow")
            return ("u256", wa * wb)
    elif op in ("B_clmul64", "B_clmul64Hi", "B_gf2Affine", "B_eor3"):
        if t1 == "u64" and t2 == "u64":
            la, lb = int(a) & MASK64, int(b) & MASK64
            if op == "B_clmul64":
                return ("u64", clmul64(la, lb))
            if op == "B_clmul64Hi":
                return ("u64", clmul64_hi(la, lb))
            if op == "B_gf2Affine":
                return ("u64", gf2_affine(la, lb))
            return ("u64", eor3_u64(la, lb))
    raise EvalUBError(f"typeError: evalBinOp {op} on {v1!r}, {v2!r}")


def eval_unary_op(op: str, v: Val) -> Val:
    t, x = v
    if op == "U_not":
        if t == "bool":
            return ("bool", not bool(x))
        if t == "u64":
            return ("u64", (~int(x)) & MASK64)
        if t == "u256":
            return ("u256", (~int(x)) & MASK256)
    elif op == "U_neg":
        if t == "u64":
            return ("u64", (-int(x)) & MASK64)
        if t == "u256":
            return ("u256", (-int(x)) & MASK256)
    elif op == "U_clz256":
        w = to_u256(v)
        if w is not None:
            return ("u256", 256 if w == 0 else 256 - w.bit_length())
    raise EvalUBError(f"typeError: evalUnaryOp {op} on {v!r}")


def eval_scalar_ast(node: ScalarAst, env: dict[int, Val]) -> Val:
    if node.kind == "u64":
        return ("u64", int(node.val) & MASK64)
    if node.kind == "bool":
        return ("bool", bool(node.val))
    if node.kind == "var":
        idx = int(node.val)
        if idx not in env:
            raise EvalUBError(f"unboundVar %{idx}")
        return env[idx]
    if node.kind == "un":
        return eval_unary_op(str(node.val), eval_scalar_ast(node.args[0], env))
    if node.kind == "sel":
        ct, cv = eval_scalar_ast(node.args[0], env)
        if ct == "bool":
            take_then = bool(cv)
        elif ct in ("u64", "u256"):
            take_then = int(cv) != 0
        else:
            raise EvalUBError(f"typeError: select condition must be bool, u64, or u256, got {ct!r}")
        return eval_scalar_ast(node.args[1] if take_then else node.args[2], env)
    if node.kind == "fma":
        va = eval_scalar_ast(node.args[0], env)
        vb = eval_scalar_ast(node.args[1], env)
        vab = eval_bin_op("B_mul", va, vb)
        vc = eval_scalar_ast(node.args[2], env)
        return eval_bin_op("B_add", vab, vc)
    if node.kind == "bin":
        l = eval_scalar_ast(node.args[0], env)
        r = eval_scalar_ast(node.args[1], env)
        return eval_bin_op(str(node.val), l, r)
    raise ValueError(f"unsupported ScalarAst node: {node}")


def parse_tuple_field_types(pty: tuple[str, ...]) -> list[tuple[str, ...]]:
    cur = Cursor(list(pty))
    if cur.next() != "T_tuple":
        return []
    cnt = cur.next_nat()
    return [parse_type(cur) for _ in range(cnt)]


def sample_tuple_field_val(fty: tuple[str, ...], seed: int, depth: int = 8) -> Val:
    r = splitmix64(seed)
    tag = fty[0]
    if tag == "T_i1":
        return ("bool", (r & 1) == 1)
    if tag in ("T_u256", "T_i256"):
        return ("u256", (r % 16) + 1)
    if depth > 0 and tag == "T_tuple":
        sub_tys = parse_tuple_field_types(fty)
        return (
            "tuple",
            tuple(sample_tuple_field_val(sub, seed + idx * 37 + 11, depth - 1) for idx, sub in enumerate(sub_tys)),
        )
    return ("u64", (r % 16) + 1)


def param_val_for_type(pty: tuple[str, ...], raw_word: int, state_idx: int = 0, p_idx: int = 0) -> Val:
    tag = pty[0]
    if tag == "T_i1":
        return ("bool", (raw_word & 1) != 0)
    if tag == "T_i8":
        return ("u64", raw_word & 0xFF)
    if tag == "T_i16":
        return ("u64", raw_word & 0xFFFF)
    if tag == "T_i32":
        return ("u64", raw_word & 0xFFFFFFFF)
    if tag in ("T_i64", "T_usize"):
        return ("u64", raw_word & MASK64)
    if tag in ("T_u256", "T_i256"):
        if state_idx < len(BOUNDARY_U256_PAIRS):
            pair = BOUNDARY_U256_PAIRS[state_idx]
            return ("u256", pair[p_idx & 1])
        b_idx = state_idx - len(BOUNDARY_U256_PAIRS)
        if b_idx < len(BOUNDARY_U256) * 2:
            return ("u256", BOUNDARY_U256[(b_idx + p_idx * 3) % len(BOUNDARY_U256)])
        w0 = raw_word & MASK64
        w1 = splitmix64(w0 ^ 1)
        w2 = splitmix64(w0 ^ 2)
        w3 = splitmix64(w0 ^ 3)
        return ("u256", w0 | (w1 << 64) | (w2 << 128) | (w3 << 192))
    if tag == "T_sarray":
        return ("sarrayId", p_idx + 1)
    if tag == "T_rawPtr":
        return ("rawPtrId", p_idx + 1)
    if tag == "T_storageMap":
        return ("storageMapId", p_idx + 1)
    if tag in ("T_objPtr", "T_taggedPtr"):
        return ("u64", 1) if (state_idx + p_idx) % 5 == 0 else ("objPtr", p_idx + 1)
    if tag == "T_tuple":
        field_tys = parse_tuple_field_types(pty)
        return (
            "tuple",
            tuple(sample_tuple_field_val(fty, (raw_word & MASK64) + idx * 17) for idx, fty in enumerate(field_tys)),
        )
    if tag in ("T_f16", "T_f32", "T_f64"):
        return ("float", (tag, raw_word & MASK64))
    if tag == "T_unit":
        return ("unit", 0)
    raise ValueError(f"unsupported LNIRType in param_val_for_type: {pty!r}")


def eval_decl_val(decl: ParsedDecl, args: list[int], state_idx: int = 0) -> Val:
    env = {
        pid: param_val_for_type(pty, val, state_idx, p_idx)
        for p_idx, ((pid, _n, _b, pty), val) in enumerate(zip(decl.params, args))
    }
    for dst, _ty, expr in decl.lets:
        env[dst] = eval_scalar_ast(expr, env)
    if decl.ret_var not in env:
        raise ValueError(f"unbound return variable %{decl.ret_var}")
    return env[decl.ret_var]


def scalar_expr_cost(node: ScalarAst, profile: dict[str, int]) -> int:
    if node.kind in ("u64", "bool", "var"):
        return 0
    if node.kind == "un":
        op_cost = profile["clz256"] if node.val == "U_clz256" else profile["bitwise"]
        return op_cost + scalar_expr_cost(node.args[0], profile)
    if node.kind == "sel":
        return profile["select"] + sum(scalar_expr_cost(a, profile) for a in node.args)
    if node.kind == "fma":
        return profile["fma"] + sum(scalar_expr_cost(a, profile) for a in node.args)
    if node.kind == "bin":
        op = str(node.val)
        lhs, rhs = node.args
        sub = scalar_expr_cost(lhs, profile) + scalar_expr_cost(rhs, profile)
        dup_penalty = 1 if (op == "B_add" and lhs == rhs) else 0
        if op in ("B_add", "B_sub"):
            return profile["addSub"] + dup_penalty + sub
        if op in ("B_bitAnd", "B_bitOr", "B_bitXor", "B_eor3"):
            return profile["bitwise"] + sub
        if op in ("B_clmul64", "B_clmul64Hi", "B_gf2Affine"):
            return 1 + sub
        if op in ("B_shl", "B_shr", "B_sar"):
            return profile["shift"] + sub
        if op in ("B_eq", "B_lt", "B_le"):
            return profile["cmp"] + sub
        if op == "B_mul":
            return profile["mul"] + sub
        if op in ("B_div", "B_mod"):
            return profile["divMod"] + sub
        if op in ("B_addChecked256", "B_subChecked256"):
            return profile["addSubChecked256"] + sub
        if op == "B_mulChecked256":
            return profile["mulChecked256"] + sub
    raise ValueError(f"unsupported ScalarAst cost node: {node}")


def decl_scalar_cost(decl: ParsedDecl, target: str) -> int:
    prof = TARGET_COST_PROFILES.get(target, TARGET_COST_PROFILES["x86_64"])
    return sum(scalar_expr_cost(expr, prof) for _dst, _ty, expr in decl.lets)


def extract_wire_response(raw_line: str) -> str | None:
    trimmed = raw_line.strip()
    if trimmed in ("", "null", "{}"):
        return None
    if trimmed.startswith("LNIR_WIRE_V1|"):
        return trimmed
    obj = json.loads(trimmed)
    if obj in (None, {}):
        return None
    if isinstance(obj, dict) and isinstance(obj.get("wire"), str) and obj["wire"].startswith("LNIR_WIRE_V1|"):
        return obj["wire"]
    raise ValueError(f"Invalid LNIR opt response payload: {trimmed!r}")


def is_word_fact_ty(ty: tuple[str, ...]) -> bool:
    return ty in (("T_i64",), ("T_usize",))


def is_raw_ptr_fact_ty(ty: tuple[str, ...]) -> bool:
    return len(ty) >= 1 and ty[0] == "T_rawPtr"


def is_excl_fact_ty(ty: tuple[str, ...]) -> bool:
    return len(ty) >= 1 and (ty[0] == "T_sarray" or ty == ("T_objPtr",))


def collect_decl_var_tys(decl: ParsedDecl) -> dict[int, tuple[str, ...]]:
    var_tys: dict[int, tuple[str, ...]] = {pid: pty for pid, _n, _b, pty in decl.params}
    for dst, ty, _expr in decl.lets:
        var_tys[dst] = ty
    return var_tys


def fact_vars_in_scope(var_tys: dict[int, tuple[str, ...]], fact: tuple[str, ...]) -> bool:
    tag = fact[0]
    if tag == "F_lt":
        ti, tn = var_tys.get(int(fact[1])), var_tys.get(int(fact[2]))
        return ti is not None and tn is not None and is_word_fact_ty(ti) and is_word_fact_ty(tn)
    if tag in ("F_add", "F_sub", "F_mul"):
        ta, tb = var_tys.get(int(fact[1])), var_tys.get(int(fact[2]))
        return ta is not None and tb is not None and is_word_fact_ty(ta) and is_word_fact_ty(tb)
    if tag == "F_aln":
        tp = var_tys.get(int(fact[1]))
        return tp is not None and (is_raw_ptr_fact_ty(tp) or is_word_fact_ty(tp))
    if tag == "F_disj":
        ta, tb = var_tys.get(int(fact[1])), var_tys.get(int(fact[2]))
        tla, tlb = var_tys.get(int(fact[3])), var_tys.get(int(fact[4]))
        return (
            ta is not None and tb is not None and tla is not None and tlb is not None
            and is_raw_ptr_fact_ty(ta) and is_raw_ptr_fact_ty(tb)
            and is_word_fact_ty(tla) and is_word_fact_ty(tlb)
        )
    if tag == "F_excl":
        to = var_tys.get(int(fact[1]))
        return to is not None and is_excl_fact_ty(to)
    return False


def check_scalar_ast_branches(node: ScalarAst, env: dict[int, Val]) -> None:
    if node.kind == "var":
        idx = int(node.val)
        if idx not in env:
            raise ValueError(f"unbound SSA variable %{idx} in candidate expression")
        return
    for ch in node.args:
        check_scalar_ast_branches(ch, env)
    if node.kind == "sel":
        for branch_idx in (1, 2):
            try:
                eval_scalar_ast(node.args[branch_idx], env)
            except EvalUBError as exc:
                msg = str(exc)
                if msg.startswith(("typeError", "unboundVar")):
                    raise ValueError(f"S_sel branch {branch_idx} failed validation: {msg}") from exc


def validate_cand_decl_static(src: ParsedDecl, cand: ParsedDecl) -> None:
    src_fact_set = set(src.facts)
    cand_var_tys = collect_decl_var_tys(cand)
    for fact in cand.facts:
        if fact not in src_fact_set:
            raise ValueError(f"Candidate fabricated RetainedFact not present in source: {fact!r}")
        if not fact_vars_in_scope(cand_var_tys, fact):
            raise ValueError(f"Candidate RetainedFact out of scope or ill-typed: {fact!r}")


def verify_opt_plugin_gate_64(src: ParsedDecl, cand: ParsedDecl, target: str) -> tuple[int, int]:
    src_sig = [(pid, pty) for pid, _n, _b, pty in src.params]
    cand_sig = [(pid, pty) for pid, _n, _b, pty in cand.params]
    if src_sig != cand_sig or src.ret_ty != cand.ret_ty:
        raise ValueError(f"Signature mismatch: {(src_sig, src.ret_ty)} != {(cand_sig, cand.ret_ty)}")
    validate_cand_decl_static(src, cand)
    arity = len(src.params)
    non_vacuous_count = 0
    for state_idx in range(64):
        vec: list[int] = []
        for p_idx in range(arity):
            if state_idx < len(BOUNDARY_U64):
                vec.append(BOUNDARY_U64[(state_idx + p_idx * 5) % len(BOUNDARY_U64)])
            else:
                vec.append(splitmix64(state_idx * 131 + p_idx * 17 + 1))
        try:
            v_src = eval_decl_val(src, vec, state_idx)
        except EvalUBError:
            continue
        non_vacuous_count += 1
        try:
            cand_env = {
                pid: param_val_for_type(pty, val, state_idx, p_idx)
                for p_idx, ((pid, _n, _b, pty), val) in enumerate(zip(cand.params, vec))
            }
            for dst, _ty, expr in cand.lets:
                check_scalar_ast_branches(expr, cand_env)
                cand_env[dst] = eval_scalar_ast(expr, cand_env)
            if cand.ret_var not in cand_env:
                raise ValueError(f"unbound return variable %{cand.ret_var}")
            v_cand = cand_env[cand.ret_var]
        except EvalUBError as exc:
            raise ValueError(
                f"64-state UB refinement violation on state {state_idx} ({vec}): src={v_src!r}, cand raised UB {exc}"
            ) from exc
        if v_src != v_cand:
            raise ValueError(f"64-state equivalence mismatch on {vec}: src={v_src!r} != cand={v_cand!r}")
    if non_vacuous_count == 0:
        raise ValueError("64-state refinement vacuous: source raised EvalUBError on all 64 samples")
    c_before = decl_scalar_cost(src, target)
    c_after = decl_scalar_cost(cand, target)
    if c_after > c_before:
        raise ValueError(f"Scalar cycle cost increased on {target}: {c_after} > {c_before}")
    return c_before, c_after


def run_single_stdio_request(cmd: list[str], line: str, timeout_ms: int) -> tuple[str | None, bool]:
    payload = line if line.endswith("\n") else line + "\n"
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        out, err = proc.communicate(payload, timeout=max(timeout_ms, 1) / 1000.0)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        return None, True
    if proc.returncode != 0:
        err_snip = (err or "").strip()
        raise RuntimeError(
            f"Plugin {cmd!r} exited with non-zero code {proc.returncode}"
            + (f": {err_snip}" if err_snip else "")
        )
    first_line = out.splitlines()[0] if out.splitlines() else ""
    return first_line, False


class AcceleratorSdkTestSuite(unittest.TestCase):
    plugin_cmd: list[str] = [sys.executable, str(DEFAULT_PLUGIN)]

    def test_01_example_config_schema(self) -> None:
        cfg_path = SDK_DIR / "accelerators.example.json"
        cfg = json.loads(cfg_path.read_text(encoding="utf-8"))
        validate_accelerator_config_dict(cfg)
        self.assertTrue(cfg["enabled"])
        self.assertGreaterEqual(len(cfg["external"]), 1)
        with self.assertRaises(ValueError):
            validate_accelerator_config_dict({"enabled": True, "bogus_field": 1})

    def test_02_tactic_accelerator_fixtures(self) -> None:
        is_default = self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]
        lines = (FIXTURES_DIR / "tactic_requests.jsonl").read_text(encoding="utf-8").splitlines()
        seen_kinds: set[str] = set()
        saw_abstain = False
        subgoal_cases: dict[str, list[str]] = {}
        for line in lines:
            if not line.strip():
                continue
            req = json.loads(line)
            out_line, timed_out = run_single_stdio_request(self.plugin_cmd, line, timeout_ms=1000)
            self.assertFalse(timed_out, f"Timed out on {req['decl_name']}")
            cert = validate_tactic_certificate(out_line or "")
            if cert is None:
                saw_abstain = True
            else:
                seen_kinds.add(cert["kind"])
                if cert["kind"] == "subgoal_cuts":
                    subgoal_cases[req["decl_name"]] = cert["cuts"]
                    for shard in cert["cuts"]:
                        self.assertIn(":=", shard)
                        header_part = shard.split(":=", 1)[0]
                        decl_kw_hits = re.findall(r"\b(?:theorem|lemma)\b", header_part)
                        self.assertEqual(len(decl_kw_hits), 1, f"Invalid or duplicate theorem/lemma header in shard: {shard!r}")
        if is_default:
            self.assertEqual(seen_kinds, {"rewritten_proof", "counterexample_found", "subgoal_cuts"})
            self.assertTrue(saw_abstain)
            self.assertEqual(
                set(subgoal_cases),
                {"sdk_cut_fission_full", "sdk_cut_fission_attr", "sdk_cut_fission_binders", "sdk_cut_fission_bare_colon"},
            )
            for shard in subgoal_cases["sdk_cut_fission_full"]:
                self.assertTrue(shard.startswith("theorem sdk_cut_fission_full (n : Nat)"), shard)
            for shard in subgoal_cases["sdk_cut_fission_attr"]:
                self.assertTrue(shard.startswith("@[simp] private lemma sdk_cut_fission_attr (n : Nat)"), shard)
            self.assertIn("(m : Nat) : m + 0 = m := by rfl", subgoal_cases["sdk_cut_fission_attr"][0])
            self.assertIn("(h1 : ∀ (m : Nat), m + 0 = m)", subgoal_cases["sdk_cut_fission_attr"][1])
            for shard in subgoal_cases["sdk_cut_fission_binders"]:
                self.assertTrue(shard.startswith("theorem sdk_cut_fission_binders (n : Nat)"), shard)
            self.assertEqual(
                subgoal_cases["sdk_cut_fission_bare_colon"][0],
                "theorem sdk_cut_fission_bare_colon : 0 + 0 = 0 := by rfl",
            )
            self.assertTrue(
                subgoal_cases["sdk_cut_fission_bare_colon"][1].startswith(
                    "theorem sdk_cut_fission_bare_colon (h1 : 0 + 0 = 0) : 0 + 0 = 0 := by"
                )
            )

    def test_03_lnir_wire_opt_fixtures_and_adversarial_gate(self) -> None:
        lines = (FIXTURES_DIR / "lnir_opt_requests.jsonl").read_text(encoding="utf-8").splitlines()
        strict_improvements = 0
        abstentions = 0
        for line in lines:
            if not line.strip():
                continue
            req = json.loads(line)
            src_decl = parse_single_decl_wire(req["wire"])
            out_line, timed_out = run_single_stdio_request(self.plugin_cmd, line, timeout_ms=1000)
            self.assertFalse(timed_out, f"Timed out on LNIR decl {req['decl_name']}")
            cand_wire = extract_wire_response(out_line or "")
            if cand_wire is None:
                abstentions += 1
                continue
            cand_decl = parse_single_decl_wire(cand_wire)
            c_before, c_after = verify_opt_plugin_gate_64(src_decl, cand_decl, req["target"])
            if c_after < c_before:
                strict_improvements += 1

        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            self.assertGreaterEqual(strict_improvements, 2)
            self.assertGreaterEqual(abstentions, 1)

        sample_req = json.loads(lines[0])
        src_sample = parse_single_decl_wire(sample_req["wire"])
        corrupt_wire = sample_req["wire"].replace("|B_mul|", "|B_sub|", 1)
        corrupt_decl = parse_single_decl_wire(corrupt_wire)
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(src_sample, corrupt_decl, "x86_64")

        self.assertEqual(eval_unary_op("U_not", ("bool", True)), ("bool", False))
        self.assertEqual(eval_unary_op("U_not", ("bool", False)), ("bool", True))
        self.assertEqual(eval_bin_op("B_sar", ("u64", 1 << 63), ("u64", 4)), ("u64", 0xF800000000000000))
        self.assertEqual(eval_bin_op("B_sar", ("u64", 1 << 63), ("u64", 0)), ("u64", 1 << 63))
        var0 = ScalarAst("var", 0)
        var1 = ScalarAst("var", 1)
        self.assertEqual(scalar_expr_cost(ScalarAst("bin", "B_add", (var0, var0)), TARGET_COST_PROFILES["x86_64"]), 2)
        self.assertEqual(scalar_expr_cost(ScalarAst("bin", "B_add", (var0, var1)), TARGET_COST_PROFILES["x86_64"]), 1)
        valid_facts_decl = parse_single_decl_wire(
            sample_req["wire"] + "|F_facts|2|F_lt|0|1|F_add|0|1|1|0"
        )
        self.assertEqual(len(valid_facts_decl.facts), 2)
        with self.assertRaises(ValueError):
            parse_single_decl_wire(sample_req["wire"] + "|F_facts|not_a_nat")
        with self.assertRaises(ValueError):
            parse_single_decl_wire(sample_req["wire"] + "|F_facts|1|F_excl|0|EXTRA_TOKEN")

        checked_same_ub_src_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|63686b5f73616d655f7562|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_add|S_var|0|S_u64|0|"
            "C_let|3|T_u256|E_scalar|S_bin|B_addChecked256|S_var|2|S_var|1|"
            "C_ret|3"
        )
        checked_same_ub_cand_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|63686b5f73616d655f7562|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|3|T_u256|E_scalar|S_bin|B_addChecked256|S_var|0|S_var|1|"
            "C_ret|3"
        )
        c_chk_before, c_chk_after = verify_opt_plugin_gate_64(
            parse_single_decl_wire(checked_same_ub_src_wire),
            parse_single_decl_wire(checked_same_ub_cand_wire),
            "x86_64",
        )
        self.assertLess(c_chk_after, c_chk_before)

        clz256_src_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|636c7a3235365f7a65726f|A_L2|0|"
            "1|0|78|0|T_u256|T_i1|"
            "C_let|1|T_u256|E_scalar|S_un|U_clz256|S_var|0|"
            "C_let|2|T_u256|E_scalar|S_bin|B_sub|S_var|0|S_var|0|"
            "C_let|3|T_u256|E_scalar|S_un|U_not|S_var|2|"
            "C_let|4|T_u256|E_scalar|S_bin|B_shr|S_var|3|S_u64|255|"
            "C_let|5|T_u256|E_scalar|S_bin|B_shl|S_var|4|S_u64|8|"
            "C_let|6|T_i1|E_scalar|S_bin|B_eq|S_var|1|S_var|5|"
            "C_ret|6"
        )
        clz256_bad_cand_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|636c7a3235365f7a65726f|A_L2|0|"
            "1|0|78|0|T_u256|T_i1|"
            "C_let|6|T_i1|E_scalar|S_bool|0|"
            "C_ret|6"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(
                parse_single_decl_wire(clz256_src_wire),
                parse_single_decl_wire(clz256_bad_cand_wire),
                "x86_64",
            )

        div_ub_intro_src_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|6469765f75625f696e74726f|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_mul|S_var|0|S_var|1|"
            "C_let|3|T_u256|E_scalar|S_bin|B_add|S_var|2|S_var|0|"
            "C_ret|3"
        )
        div_ub_intro_cand_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|6469765f75625f696e74726f|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|3|T_u256|E_scalar|S_bin|B_div|S_var|0|S_var|1|"
            "C_ret|3"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(
                parse_single_decl_wire(div_ub_intro_src_wire),
                parse_single_decl_wire(div_ub_intro_cand_wire),
                "x86_64",
            )

        ub_erasing_src_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|75625f726566696e65|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_addChecked256|S_var|0|S_var|1|"
            "C_ret|2"
        )
        ub_erasing_cand_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|75625f726566696e65|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_add|S_var|0|S_var|1|"
            "C_ret|2"
        )
        ub_src_decl = parse_single_decl_wire(ub_erasing_src_wire)
        ub_cand_decl = parse_single_decl_wire(ub_erasing_cand_wire)
        c_ub_before, c_ub_after = verify_opt_plugin_gate_64(ub_src_decl, ub_cand_decl, "x86_64")
        self.assertLess(c_ub_after, c_ub_before)

        ub_intro_src_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|75625f696e74726f|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_mul|S_var|0|S_var|1|"
            "C_let|3|T_u256|E_scalar|S_bin|B_add|S_var|0|S_var|1|"
            "C_ret|3"
        )
        ub_intro_cand_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|75625f696e74726f|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|3|T_u256|E_scalar|S_bin|B_addChecked256|S_var|0|S_var|1|"
            "C_ret|3"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(
                parse_single_decl_wire(ub_intro_src_wire),
                parse_single_decl_wire(ub_intro_cand_wire),
                "x86_64",
            )

        always_ub_wire = (
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|616c776179735f7562|A_L2|0|"
            "1|0|61|0|T_u256|T_u256|"
            "C_let|1|T_u256|E_scalar|S_bin|B_sub|S_var|0|S_var|0|"
            "C_let|2|T_u256|E_scalar|S_bin|B_div|S_var|0|S_var|1|"
            "C_ret|2"
        )
        always_ub_decl = parse_single_decl_wire(always_ub_wire)
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(always_ub_decl, always_ub_decl, "x86_64")

        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            trap_dce_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|747261705f646365|A_L2|0|"
                "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
                "C_let|2|T_u256|E_scalar|S_bin|B_addChecked256|S_var|0|S_var|1|"
                "C_let|3|T_u256|E_scalar|S_bin|B_div|S_var|0|S_var|1|"
                "C_ret|0"
            )
            t_out, t_to = run_single_stdio_request(
                self.plugin_cmd,
                json.dumps({"decl_name": "trap_dce", "target": "x86_64", "budget_ms": 50, "wire": trap_dce_wire}),
                timeout_ms=1000,
            )
            self.assertFalse(t_to)
            self.assertIsNone(extract_wire_response(t_out or ""))

            bool_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|626f6f6c5f6e6f6f70|A_L2|0|"
                "1|0|62|0|T_i1|T_i1|C_let|1|T_i1|E_scalar|S_un|U_not|S_var|0|C_ret|1"
            )
            b_out, b_to = run_single_stdio_request(
                self.plugin_cmd,
                json.dumps({"decl_name": "bool_noop", "target": "x86_64", "budget_ms": 50, "wire": bool_wire}),
                timeout_ms=1000,
            )
            self.assertFalse(b_to)
            self.assertIsNone(extract_wire_response(b_out or ""))

            rhs_fma_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|7268735f666d61|A_L2|0|"
                "3|0|61|0|T_i64|1|62|0|T_i64|2|63|0|T_i64|T_i64|"
                "C_let|3|T_i64|E_scalar|S_bin|B_add|S_var|0|S_var|0|"
                "C_let|4|T_i64|E_scalar|S_bin|B_mul|S_var|1|S_var|2|"
                "C_let|5|T_i64|E_scalar|S_bin|B_add|S_var|3|S_var|4|C_ret|5"
            )
            f_out, f_to = run_single_stdio_request(
                self.plugin_cmd,
                json.dumps({"decl_name": "rhs_fma", "target": "arm64", "budget_ms": 50, "wire": rhs_fma_wire}),
                timeout_ms=1000,
            )
            self.assertFalse(f_to)
            f_cand_wire = extract_wire_response(f_out or "")
            self.assertIsNotNone(f_cand_wire)
            f_src = parse_single_decl_wire(rhs_fma_wire)
            f_cand = parse_single_decl_wire(f_cand_wire or "")
            c0, c1 = verify_opt_plugin_gate_64(f_src, f_cand, "arm64")
            self.assertLess(c1, c0)
            self.assertIn("|S_fma|S_var|1|S_var|2|S_var|3|", f_cand_wire or "")

    def test_04_malformed_and_adversarial_inputs_fail_safe(self) -> None:
        adv_lines = [
            ln for ln in (FIXTURES_DIR / "adversarial_requests.jsonl").read_text(encoding="utf-8").splitlines()
            if ln.strip()
        ]
        for ln in adv_lines:
            out_line, timed_out = run_single_stdio_request(self.plugin_cmd, ln, timeout_ms=500)
            self.assertFalse(timed_out)
            if out_line:
                self.assertIsNone(validate_tactic_certificate(out_line))
        for bad_budget in (False, True):
            b_line = json.dumps({
                "decl_name": "bool_budget_tactic",
                "stmt_src": "theorem bool_budget_tactic (a b : Nat) (h1 : a = b) : a + 0 = b",
                "body_src": "by simp [h1]",
                "imports_csv": "Init",
                "available_constants": ["Nat.add_zero", "h1"],
                "budget_ms": bad_budget,
            })
            out_line, timed_out = run_single_stdio_request(self.plugin_cmd, b_line, timeout_ms=500)
            self.assertFalse(timed_out)
            self.assertIsNone(validate_tactic_certificate(out_line or ""))

        valid_probe = json.dumps({
            "decl_name": "stream_survival_probe",
            "stmt_src": "theorem stream_survival_probe (a b : Nat) (h1 : a = b) : a + 0 = b",
            "body_src": "by simp [h1]",
            "imports_csv": "Init",
            "available_constants": ["Nat.add_zero", "h1"],
            "budget_ms": 25,
        })
        batch_lines = [*adv_lines, valid_probe]
        proc = subprocess.Popen(
            self.plugin_cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        out, err = proc.communicate("\n".join(batch_lines) + "\n", timeout=3.0)
        self.assertEqual(proc.returncode, 0, f"Plugin crashed on adversarial JSONL stream: {err}")
        resp_lines = [ln for ln in out.splitlines() if ln.strip()]
        self.assertEqual(len(resp_lines), len(batch_lines))
        for ln in resp_lines[:-1]:
            self.assertIsNone(validate_tactic_certificate(ln))
        probe_cert = validate_tactic_certificate(resp_lines[-1])
        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            self.assertIsNotNone(probe_cert)

        crashing_cmd = [sys.executable, "-c", "import sys; sys.stderr.write('boom\\n'); raise SystemExit(2)"]
        with self.assertRaises(RuntimeError):
            run_single_stdio_request(crashing_cmd, valid_probe, timeout_ms=500)

    def test_05_timeout_and_kill_isolation(self) -> None:
        hang_cmd = [sys.executable, str(DEFAULT_PLUGIN), "--simulate-hang-ms", "5000"]
        t0 = time.monotonic()
        out_line, timed_out = run_single_stdio_request(
            hang_cmd,
            '{"decl_name":"hang_probe","stmt_src":"True","body_src":"by trivial","imports_csv":"Init","available_constants":[],"budget_ms":40}',
            timeout_ms=40,
        )
        elapsed_ms = (time.monotonic() - t0) * 1000.0
        self.assertTrue(timed_out)
        self.assertIsNone(out_line)
        self.assertLess(elapsed_ms, 1500.0)

        probe = '{"decl_name":"budget_eof_probe","stmt_src":"theorem budget_eof_probe : True","body_src":"by trivial","imports_csv":"Init","available_constants":[],"budget_ms":25}'
        t1 = time.monotonic()
        p_out, p_timed_out = run_single_stdio_request(self.plugin_cmd, probe, timeout_ms=500)
        p_elapsed_ms = (time.monotonic() - t1) * 1000.0
        self.assertFalse(p_timed_out)
        self.assertLess(p_elapsed_ms, 500.0)
        validate_tactic_certificate(p_out or "")

        eof_proc = subprocess.Popen(
            self.plugin_cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        eof_out, eof_err = eof_proc.communicate("", timeout=1.0)
        self.assertEqual(eof_proc.returncode, 0, eof_err)
        self.assertEqual(eof_out.strip(), "")

        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            oneshot_cmd = [*self.plugin_cmd, "--one-shot"]
            valid_two = (
                '{"decl_name":"os1","stmt_src":"theorem os1 (a b : Nat) (h1 : a = b) : a + 0 = b","body_src":"by simp [h1]","imports_csv":"Init","available_constants":["Nat.add_zero","h1"],"budget_ms":25}\n'
                '{"decl_name":"os2","stmt_src":"theorem os2 (a b : Nat) (h1 : a = b) : a + 0 = b","body_src":"by simp [h1]","imports_csv":"Init","available_constants":["Nat.add_zero","h1"],"budget_ms":25}\n'
            )
            os_proc = subprocess.Popen(
                oneshot_cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            os_out, os_err = os_proc.communicate(valid_two, timeout=1.0)
            self.assertEqual(os_proc.returncode, 0, os_err)
            os_lines = [ln for ln in os_out.splitlines() if ln.strip()]
            self.assertEqual(len(os_lines), 1)
            self.assertIsNotNone(validate_tactic_certificate(os_lines[0]))

            os_adv_out, os_adv_to = run_single_stdio_request(oneshot_cmd, "{not-valid-json", timeout_ms=500)
            self.assertFalse(os_adv_to)
            self.assertIsNone(validate_tactic_certificate(os_adv_out or ""))

    def test_06_reviewer_regressions_p1_and_p2(self) -> None:
        is_default = self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]

        # P1-B.1: 256-bit shift semantics in eval_bin_op & 64-state gate
        self.assertEqual(eval_bin_op("B_shl", ("u256", 3), ("u256", 2)), ("u256", 12))
        self.assertEqual(eval_bin_op("B_shl", ("u256", 3), ("u256", 256)), ("u256", 0))
        self.assertEqual(eval_bin_op("B_shl", ("u256", 3), ("u64", 0)), ("u256", 3))
        self.assertEqual(eval_bin_op("B_shr", ("u256", 12), ("u256", 2)), ("u256", 3))
        self.assertEqual(eval_bin_op("B_shr", ("u256", 12), ("u64", 0)), ("u256", 12))
        self.assertEqual(eval_bin_op("B_sar", ("u256", 1 << 255), ("u256", 1)), ("u256", 3 << 254))
        self.assertEqual(eval_bin_op("B_sar", ("u256", 1 << 255), ("u256", 0)), ("u256", 1 << 255))
        with self.assertRaises(EvalUBError):
            eval_bin_op("B_shl", ("u256", 3), ("u64", 1))
        with self.assertRaises(EvalUBError):
            eval_bin_op("B_shr", ("u256", 3), ("u64", 1))
        with self.assertRaises(EvalUBError):
            eval_bin_op("B_sar", ("u256", 3), ("u64", 0))
        with self.assertRaises(EvalUBError):
            eval_bin_op("B_sar", ("u256", 3), ("u64", 1))

        # Rewriting u256 `x + x` into `B_shl(x, S_u64(1))` MUST FAIL the 64-input gate (typeError UB)
        u256_add_src = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|753235365f616464|A_L2|0|"
            "1|0|78|0|T_u256|T_u256|C_let|1|T_u256|E_scalar|S_bin|B_add|S_var|0|S_var|0|C_ret|1"
        )
        u256_bad_shl_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|753235365f616464|A_L2|0|"
            "1|0|78|0|T_u256|T_u256|C_let|1|T_u256|E_scalar|S_bin|B_shl|S_var|0|S_u64|1|C_ret|1"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(u256_add_src, u256_bad_shl_cand, "x86_64")

        # Valid `(T_u256, T_u256)` shift must NOT crash validate.py
        u256_shl_src = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|753235365f73686c|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|2|T_u256|E_scalar|S_bin|B_add|S_var|0|S_u64|0|"
            "C_let|3|T_u256|E_scalar|S_bin|B_shl|S_var|2|S_var|1|C_ret|3"
        )
        u256_shl_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|753235365f73686c|A_L2|0|"
            "2|0|61|0|T_u256|1|62|0|T_u256|T_u256|"
            "C_let|3|T_u256|E_scalar|S_bin|B_shl|S_var|0|S_var|1|C_ret|3"
        )
        c_shl_before, c_shl_after = verify_opt_plugin_gate_64(u256_shl_src, u256_shl_cand, "x86_64")
        self.assertLess(c_shl_after, c_shl_before)

        # P1-B.2: Non-u64 parameter types (`T_sarray`, `T_rawPtr`, `T_objPtr`, `T_taggedPtr`,
        # `T_storageMap`, `T_tuple`, `T_f16`, `T_f32`, `T_f64`) must not be sampled as raw u64 words;
        # rewriting `B_sub(p0, 0)` to `B_bitAnd(p0, MASK64)` on `T_sarray` must FAIL.
        for non_u64_ty_toks in (
            "T_sarray|T_i8",
            "T_rawPtr|T_i8",
            "T_objPtr",
            "T_taggedPtr",
            "T_storageMap",
            "T_tuple|1|T_i64",
            "T_f16",
            "T_f32",
            "T_f64",
        ):
            sarr_src = parse_single_decl_wire(
                f"LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|6e6f6e5f753634|A_L2|0|"
                f"1|0|70|0|{non_u64_ty_toks}|{non_u64_ty_toks}|"
                f"C_let|1|{non_u64_ty_toks}|E_scalar|S_bin|B_sub|S_var|0|S_u64|0|C_ret|1"
            )
            sarr_bad_cand = parse_single_decl_wire(
                f"LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|6e6f6e5f753634|A_L2|0|"
                f"1|0|70|0|{non_u64_ty_toks}|{non_u64_ty_toks}|"
                f"C_let|1|{non_u64_ty_toks}|E_scalar|S_bin|B_bitAnd|S_var|0|S_u64|{MASK64}|C_ret|1"
            )
            with self.assertRaises(ValueError, msg=f"Failed to reject bitAnd mask on {non_u64_ty_toks}"):
                verify_opt_plugin_gate_64(sarr_src, sarr_bad_cand, "x86_64")

        # P2.3: verify_opt_plugin_gate_64 must evaluate both S_sel branches (catching unbound SSA / ill-typed dead branch)
        sel_src = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|73656c5f67617465|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|C_let|1|T_i64|E_scalar|S_bin|B_add|S_var|0|S_u64|0|C_ret|1"
        )
        sel_unbound_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|73656c5f67617465|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|C_let|1|T_i64|E_scalar|S_sel|S_bool|1|S_var|0|S_var|99|C_ret|1"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(sel_src, sel_unbound_cand, "x86_64")

        sel_illtyped_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|73656c5f67617465|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|C_let|1|T_i64|E_scalar|S_sel|S_bool|1|S_var|0|S_bin|B_lt|S_bool|1|S_bool|0|C_ret|1"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(sel_src, sel_illtyped_cand, "x86_64")

        # P2.3b: verify_opt_plugin_gate_64 must reject fabricated or out-of-scope F_facts
        fabricated_fact_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|73656c5f67617465|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|C_let|1|T_i64|E_scalar|S_var|0|C_ret|1|F_facts|1|F_add|0|0|1|1"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(sel_src, fabricated_fact_cand, "x86_64")

        out_of_scope_fact_src = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|666163745f73636f7065|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|"
            "C_let|1|T_i64|E_scalar|S_bin|B_add|S_var|0|S_u64|0|"
            "C_let|2|T_i64|E_scalar|S_var|0|C_ret|2|F_facts|1|F_lt|0|1"
        )
        out_of_scope_fact_cand = parse_single_decl_wire(
            "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|666163745f73636f7065|A_L2|0|"
            "1|0|78|0|T_i64|T_i64|"
            "C_let|2|T_i64|E_scalar|S_var|0|C_ret|2|F_facts|1|F_lt|0|1"
        )
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(out_of_scope_fact_src, out_of_scope_fact_cand, "x86_64")

        if is_default:
            import importlib.util
            spec = importlib.util.spec_from_file_location("sdk_plugin_mod", DEFAULT_PLUGIN)
            assert spec is not None and spec.loader is not None
            mod = importlib.util.module_from_spec(spec)
            sys.modules["sdk_plugin_mod"] = mod
            spec.loader.exec_module(mod)

            # P1-A.1: Idiomatic multiline `have` block with indented sub-tactics
            cuts_multi = mod.extract_have_cuts(
                "multi_have",
                "theorem multi_have (n : Nat) : n + 0 = n",
                "by\n  have h1 : n + 0 = n := by\n    rfl\n  exact h1",
            )
            self.assertEqual(
                cuts_multi,
                [
                    "theorem multi_have (n : Nat) : n + 0 = n := by\n  rfl",
                    "theorem multi_have (n : Nat) (h1 : n + 0 = n) : n + 0 = n := by\n  exact h1",
                ],
            )

            # P1-A.2: Binder collision rejection (`theorem foo (h1 : Nat)` with `have h1 : 0 = 0`)
            cuts_collide = mod.extract_have_cuts(
                "foo",
                "theorem foo (h1 : Nat) : 0 = 0",
                "by\n  have h1 : 0 = 0 := by rfl\n  exact h1",
            )
            self.assertEqual(cuts_collide, [])

            # Also reject collision between two `have` cuts (`have h1 ...` then `have h1 ...`)
            cuts_dup_have = mod.extract_have_cuts(
                "foo_dup",
                "theorem foo_dup (n : Nat) : 0 = 0",
                "by\n  have h1 : 0 = 0 := by rfl\n  have h1 : 0 = 0 := by rfl\n  exact h1",
            )
            self.assertEqual(cuts_dup_have, [])

            # P1-A.3: `split_top_level_colon` must ignore colons inside `«...»` guillemets and `':'` char literals
            self.assertEqual(
                mod.split_top_level_colon("theorem «foo:bar» (c : Char := ':') : c = ':'"),
                ("theorem «foo:bar» (c : Char := ':')", "c = ':'"),
            )
            cuts_guillemet = mod.extract_have_cuts(
                "«foo:bar»",
                "theorem «foo:bar» : ':' = ':'",
                "by\n  have «h:1» : ':' = ':' := by rfl\n  exact «h:1»",
            )
            self.assertEqual(
                cuts_guillemet,
                [
                    "theorem «foo:bar» : ':' = ':' := by rfl",
                    "theorem «foo:bar» («h:1» : ':' = ':') : ':' = ':' := by\n  exact «h:1»",
                ],
            )

            # P2.1: SSA variable rebind (`dst` rebound) must use latest binding and DCE dead first rebind
            rebind_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|726562696e64|A_L2|0|"
                "2|0|61|0|T_i64|1|62|0|T_i64|T_i64|"
                "C_let|2|T_i64|E_scalar|S_var|0|"
                "C_let|2|T_i64|E_scalar|S_bin|B_add|S_var|1|S_u64|0|"
                "C_let|3|T_i64|E_scalar|S_var|2|C_ret|3"
            )
            rb_resp = mod.handle_lnir_opt_request(
                {"decl_name": "rebind", "target": "x86_64", "budget_ms": 50, "wire": rebind_wire}
            )
            self.assertIn("wire", rb_resp)
            rb_src = parse_single_decl_wire(rebind_wire)
            rb_cand = parse_single_decl_wire(rb_resp["wire"])
            verify_opt_plugin_gate_64(rb_src, rb_cand, "x86_64")
            self.assertEqual(rb_cand.lets, [])
            self.assertEqual(rb_cand.ret_var, 1)

            # P2.1b: Rebinding a parameter id (`0`) must not fold later `S_var|0` back to pre-rebind `S_var|0`!
            rebind_param_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|726562696e645f70|A_L2|0|"
                "2|0|61|0|T_i64|1|62|0|T_i64|T_i64|"
                "C_let|2|T_i64|E_scalar|S_var|0|"
                "C_let|0|T_i64|E_scalar|S_var|1|"
                "C_let|3|T_i64|E_scalar|S_bin|B_add|S_var|2|S_var|0|C_ret|3"
            )
            rbp_resp = mod.handle_lnir_opt_request(
                {"decl_name": "rebind_p", "target": "x86_64", "budget_ms": 50, "wire": rebind_param_wire}
            )
            if "wire" in rbp_resp:
                verify_opt_plugin_gate_64(
                    parse_single_decl_wire(rebind_param_wire),
                    parse_single_decl_wire(rbp_resp["wire"]),
                    "x86_64",
                )

            # P2.2: Multi-use `B_mul` must NOT be inlined into `S_fma` when it increases scalar cost on `target`
            multi_mul_wire = (
                "LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|6d756c74695f6d756c|A_L2|0|"
                "3|0|61|0|T_i64|1|62|0|T_i64|2|63|0|T_i64|T_i64|"
                "C_let|3|T_i64|E_scalar|S_bin|B_mul|S_var|0|S_var|1|"
                "C_let|4|T_i64|E_scalar|S_bin|B_add|S_var|3|S_var|2|"
                "C_let|5|T_i64|E_scalar|S_bin|B_bitXor|S_var|4|S_var|3|C_ret|5"
            )
            for tgt in ("x86_64", "arm64", "cuda_ptx", "apple_metal"):
                mm_resp = mod.handle_lnir_opt_request(
                    {"decl_name": "multi_mul", "target": tgt, "budget_ms": 50, "wire": multi_mul_wire}
                )
                if "wire" in mm_resp:
                    verify_opt_plugin_gate_64(
                        parse_single_decl_wire(multi_mul_wire),
                        parse_single_decl_wire(mm_resp["wire"]),
                        tgt,
                    )


def resolve_plugin_cmd(raw: str | None) -> list[str]:
    if not raw:
        return [sys.executable, str(DEFAULT_PLUGIN)]
    parts = shlex.split(raw)
    if len(parts) == 1 and parts[0].endswith(".py"):
        return [sys.executable, parts[0]]
    return parts


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--plugin-cmd",
        default=None,
        help="Command string to launch the plugin under test (default: `<python3> sdk/accelerator-template/plugin.py`)",
    )
    args = ap.parse_args()
    AcceleratorSdkTestSuite.plugin_cmd = resolve_plugin_cmd(args.plugin_cmd)
    t0 = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(AcceleratorSdkTestSuite)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    dt_ms = (time.monotonic() - t0) * 1000.0
    if not result.wasSuccessful():
        return 1
    print(f"[sdk/accelerator-template] OK ({result.testsRun} checks passed in {dt_ms:.1f} ms)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
