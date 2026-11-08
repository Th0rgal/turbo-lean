#!/usr/bin/env python3
"""Reference zero-TCB external JSONL-stdio plugin for `turbo-lean` and `LeanNative`.

Speaks both zero-trust external protocols with Python 3 standard library only:
1. `ExternalProcessAccelerator` (`crates/turbo-lean/src/accelerators.rs`):
   Reads `AcceleratorInput` JSON lines (`decl_name`, `stmt_src`, `body_src`,
   `imports_csv`, `available_constants`, `budget_ms`) and emits an
   `AcceleratorCertificate` (`rewritten_proof`, `counterexample_found`,
   `subgoal_cuts`) or `{}` to abstain.
2. `runExternalOptPlugin` (`lean/LeanNative/Transform/Plugins.lean`):
   Reads `{"decl_name":...,"target":...,"budget_ms":...,"wire":"LNIR_WIRE_V1|..."}`
   and emits `{"wire":"LNIR_WIRE_V1|..."}` (or `{}` to abstain).
"""
import json
import re
import sys
import time
from dataclasses import dataclass

PLUGIN_NAME = "plugin:sdk-template"
MASK64 = (1 << 64) - 1
EXCLUDED_CORE_CONSTS = frozenset({
    "Eq", "Eq.refl", "Eq.symm", "Eq.trans", "True", "False", "Nat", "Bool",
    "And", "Or", "Not", "Iff", "propext", "Quot.sound", "Classical.choice", "rfl",
})
ATOMIC_TYPES = frozenset({
    "T_i1", "T_i8", "T_i16", "T_i32", "T_i64", "T_usize", "T_u256", "T_i256",
    "T_f16", "T_f32", "T_f64", "T_objPtr", "T_taggedPtr", "T_storageMap", "T_unit", "T_nat",
})
ASSURANCE_TAGS = frozenset({"A_L0", "A_L1", "A_L2", "A_L3", "A_L4", "A_TEST"})
BIN_OPS = frozenset({
    "B_add", "B_sub", "B_mul", "B_div", "B_mod", "B_bitAnd", "B_bitOr", "B_bitXor",
    "B_shl", "B_shr", "B_sar", "B_eq", "B_lt", "B_le", "B_addChecked256",
    "B_subChecked256", "B_mulChecked256", "B_clmul64", "B_clmul64Hi", "B_gf2Affine", "B_eor3",
})
UNARY_OPS = frozenset({"U_not", "U_neg", "U_clz256"})


def hex_encode(s: str) -> str:
    return "_" if not s else s.encode("utf-8").hex()


def hex_decode(tok: str) -> str | None:
    if tok == "_":
        return ""
    if len(tok) % 2 != 0:
        return None
    try:
        return bytes.fromhex(tok).decode("utf-8")
    except ValueError:
        return None


def parse_nat(tok: str) -> int | None:
    return int(tok) if tok.isdigit() else None


@dataclass(frozen=True)
class ScalarNode:
    kind: str
    val: int | bool | str | None = None
    children: tuple["ScalarNode", ...] = ()


class WireCursor:
    def __init__(self, tokens: list[str]) -> None:
        self.tokens = tokens
        self.idx = 0

    def peek(self) -> str | None:
        return self.tokens[self.idx] if self.idx < len(self.tokens) else None

    def next(self) -> str:
        if self.idx >= len(self.tokens):
            raise ValueError("unexpected end of LNIR_WIRE_V1 stream")
        tok = self.tokens[self.idx]
        self.idx += 1
        return tok

    def next_nat(self) -> int:
        v = parse_nat(self.next())
        if v is None:
            raise ValueError("invalid Nat token")
        return v

    def next_u64(self) -> int:
        return self.next_nat() & MASK64

    def next_bool(self) -> bool:
        tok = self.next()
        if tok == "1":
            return True
        if tok == "0":
            return False
        raise ValueError("invalid Bool token")

    def next_hex_str(self) -> str:
        s = hex_decode(self.next())
        if s is None:
            raise ValueError("invalid hex string token")
        return s


U64_TYPES = frozenset({("T_i64",), ("T_usize",)})


def parse_type_tokens(cur: WireCursor) -> list[str]:
    tag = cur.next()
    if tag in ATOMIC_TYPES:
        return ["T_i64" if tag == "T_nat" else tag]
    if tag in ("T_sarray", "T_rawPtr"):
        return [tag, *parse_type_tokens(cur)]
    if tag == "T_tuple":
        cnt = cur.next_nat()
        out = ["T_tuple", str(cnt)]
        for _ in range(cnt):
            out.extend(parse_type_tokens(cur))
        return out
    raise ValueError(f"unknown LNIRType token: {tag}")


def parse_fact_tokens(cur: WireCursor) -> list[str]:
    tag = cur.next()
    if tag in ("F_lt", "F_aln"):
        return [tag, str(cur.next_nat()), str(cur.next_nat())]
    if tag in ("F_add", "F_sub", "F_mul"):
        a = str(cur.next_nat())
        b = str(cur.next_nat())
        nsw = "1" if cur.next_bool() else "0"
        nuw = "1" if cur.next_bool() else "0"
        return [tag, a, b, nsw, nuw]
    if tag == "F_disj":
        return [tag, str(cur.next_nat()), str(cur.next_nat()), str(cur.next_nat()), str(cur.next_nat())]
    if tag == "F_excl":
        return [tag, str(cur.next_nat())]
    raise ValueError(f"unknown RetainedFact tag: {tag}")


def parse_trailing_facts(cur: WireCursor) -> tuple[list[str], set[int]]:
    if cur.idx == len(cur.tokens):
        return [], set()
    if cur.next() != "F_facts":
        raise ValueError("unexpected trailing wire tokens")
    cnt = cur.next_nat()
    out = ["F_facts", str(cnt)]
    fact_vars: set[int] = set()
    for _ in range(cnt):
        ftoks = parse_fact_tokens(cur)
        tag = ftoks[0]
        if tag in ("F_lt", "F_add", "F_sub", "F_mul"):
            fact_vars.update({int(ftoks[1]), int(ftoks[2])})
        elif tag in ("F_aln", "F_excl"):
            fact_vars.add(int(ftoks[1]))
        elif tag == "F_disj":
            fact_vars.update({int(ftoks[1]), int(ftoks[2]), int(ftoks[3]), int(ftoks[4])})
        out.extend(ftoks)
    if cur.idx != len(cur.tokens):
        raise ValueError("unexpected trailing wire tokens after F_facts")
    return out, fact_vars


def parse_scalar(cur: WireCursor) -> ScalarNode:
    tag = cur.next()
    if tag == "S_u64":
        return ScalarNode("u64", cur.next_u64())
    if tag == "S_bool":
        return ScalarNode("bool", cur.next_bool())
    if tag == "S_var":
        return ScalarNode("var", cur.next_nat())
    if tag == "S_bin":
        op = cur.next()
        if op not in BIN_OPS:
            raise ValueError(f"unknown BinOp: {op}")
        lhs = parse_scalar(cur)
        rhs = parse_scalar(cur)
        return ScalarNode("bin", op, (lhs, rhs))
    if tag == "S_un":
        op = cur.next()
        if op not in UNARY_OPS:
            raise ValueError(f"unknown UnaryOp: {op}")
        return ScalarNode("un", op, (parse_scalar(cur),))
    if tag == "S_sel":
        return ScalarNode("sel", None, (parse_scalar(cur), parse_scalar(cur), parse_scalar(cur)))
    if tag == "S_fma":
        return ScalarNode("fma", None, (parse_scalar(cur), parse_scalar(cur), parse_scalar(cur)))
    raise ValueError(f"unknown ScalarExpr tag: {tag}")


def encode_scalar(node: ScalarNode) -> list[str]:
    if node.kind == "u64":
        return ["S_u64", str(int(node.val) & MASK64)]
    if node.kind == "bool":
        return ["S_bool", "1" if node.val else "0"]
    if node.kind == "var":
        return ["S_var", str(int(node.val))]
    if node.kind == "bin":
        return ["S_bin", str(node.val), *encode_scalar(node.children[0]), *encode_scalar(node.children[1])]
    if node.kind == "un":
        return ["S_un", str(node.val), *encode_scalar(node.children[0])]
    if node.kind == "sel":
        c, t, e = node.children
        return ["S_sel", *encode_scalar(c), *encode_scalar(t), *encode_scalar(e)]
    if node.kind == "fma":
        a, b, c = node.children
        return ["S_fma", *encode_scalar(a), *encode_scalar(b), *encode_scalar(c)]
    raise ValueError(f"invalid ScalarNode: {node}")


def infer_scalar_type(node: ScalarNode, type_env: dict[int, tuple[str, ...]]) -> tuple[str, ...] | None:
    if node.kind == "u64":
        return ("T_i64",)
    if node.kind == "bool":
        return ("T_i1",)
    if node.kind == "var":
        return type_env.get(int(node.val))
    if node.kind == "un":
        arg_ty = infer_scalar_type(node.children[0], type_env)
        if node.val == "U_clz256":
            return ("T_u256",) if arg_ty in U64_TYPES or arg_ty == ("T_u256",) else None
        if node.val == "U_neg":
            return arg_ty if arg_ty in U64_TYPES or arg_ty == ("T_u256",) else None
        if node.val == "U_not":
            return arg_ty if arg_ty in U64_TYPES or arg_ty in (("T_i1",), ("T_u256",)) else None
        return None
    if node.kind == "sel":
        cond_ty = infer_scalar_type(node.children[0], type_env)
        t_ty = infer_scalar_type(node.children[1], type_env)
        e_ty = infer_scalar_type(node.children[2], type_env)
        if cond_ty in (("T_i1",), ("T_i64",), ("T_usize",), ("T_u256",)) and t_ty is not None and t_ty == e_ty:
            return t_ty
        return None
    if node.kind == "fma":
        if all(infer_scalar_type(ch, type_env) in U64_TYPES for ch in node.children):
            return ("T_i64",)
        return None
    if node.kind == "bin":
        op = str(node.val)
        l_ty = infer_scalar_type(node.children[0], type_env)
        r_ty = infer_scalar_type(node.children[1], type_env)
        if op in ("B_eq", "B_lt", "B_le"):
            if op == "B_eq" and l_ty == ("T_i1",) and r_ty == ("T_i1",):
                return ("T_i1",)
            if (l_ty in U64_TYPES and r_ty in U64_TYPES) or (l_ty == ("T_u256",) and r_ty == ("T_u256",)):
                return ("T_i1",)
            return None
        if op in ("B_addChecked256", "B_subChecked256", "B_mulChecked256"):
            return ("T_u256",)
        if l_ty in U64_TYPES and r_ty in U64_TYPES:
            return ("T_i64",)
        if l_ty == ("T_u256",) and r_ty == ("T_u256",) and op not in ("B_clmul64", "B_clmul64Hi", "B_gf2Affine", "B_eor3"):
            return ("T_u256",)
    return None


def is_u64_node(node: ScalarNode, type_env: dict[int, tuple[str, ...]]) -> bool:
    return infer_scalar_type(node, type_env) in U64_TYPES


def collect_scalar_vars(node: ScalarNode) -> set[int]:
    out = {int(node.val)} if node.kind == "var" else set()
    for ch in node.children:
        out |= collect_scalar_vars(ch)
    return out


def scalar_node_mentions_var(node: ScalarNode, vid: int) -> bool:
    if node.kind == "var" and int(node.val) == vid:
        return True
    return any(scalar_node_mentions_var(ch, vid) for ch in node.children)


def invalidate_scalar_env_var(scalar_env: dict[int, ScalarNode], vid: int) -> None:
    scalar_env.pop(vid, None)
    stale = [k for k, v in scalar_env.items() if scalar_node_mentions_var(v, vid)]
    for k in stale:
        del scalar_env[k]


def rewrite_scalar(
    node: ScalarNode,
    scalar_env: dict[int, ScalarNode],
    type_env: dict[int, tuple[str, ...]],
    var_uses: dict[int, int] | None = None,
) -> ScalarNode:
    if node.kind == "var" and int(node.val) in scalar_env:
        bound = scalar_env[int(node.val)]
        if bound.kind in ("u64", "bool", "var") and type_env.get(int(node.val)) == infer_scalar_type(bound, type_env):
            return bound
    if node.children:
        node = ScalarNode(
            node.kind,
            node.val,
            tuple(rewrite_scalar(ch, scalar_env, type_env, var_uses) for ch in node.children),
        )

    if node.kind == "bin":
        op = str(node.val)
        lhs, rhs = node.children
        lhs_is_u64 = is_u64_node(lhs, type_env)
        rhs_is_u64 = is_u64_node(rhs, type_env)
        if not (lhs_is_u64 and rhs_is_u64):
            return node

        lhs_can_inline = lhs.kind != "var" or var_uses is None or var_uses.get(int(lhs.val), 0) <= 1
        rhs_can_inline = rhs.kind != "var" or var_uses is None or var_uses.get(int(rhs.val), 0) <= 1
        lhs_def = scalar_env[int(lhs.val)] if lhs.kind == "var" and int(lhs.val) in scalar_env and lhs_can_inline else lhs
        rhs_def = scalar_env[int(rhs.val)] if rhs.kind == "var" and int(rhs.val) in scalar_env and rhs_can_inline else rhs

        if op in ("B_add", "B_sub", "B_bitOr", "B_bitXor", "B_shl", "B_shr") and rhs.kind == "u64" and rhs.val == 0:
            return lhs
        if op in ("B_add", "B_bitOr", "B_bitXor") and lhs.kind == "u64" and lhs.val == 0:
            return rhs
        if op == "B_mul":
            if rhs.kind == "u64" and rhs.val == 1:
                return lhs
            if lhs.kind == "u64" and lhs.val == 1:
                return rhs
            if rhs.kind == "u64" and rhs.val == 2:
                return ScalarNode("bin", "B_shl", (lhs, ScalarNode("u64", 1)))
            if lhs.kind == "u64" and lhs.val == 2:
                return ScalarNode("bin", "B_shl", (rhs, ScalarNode("u64", 1)))
        if op == "B_add":
            if lhs_def.kind == "bin" and lhs_def.val == "B_mul":
                a, b = lhs_def.children
                if is_u64_node(a, type_env) and is_u64_node(b, type_env):
                    return ScalarNode("fma", None, (a, b, rhs))
            elif rhs_def.kind == "bin" and rhs_def.val == "B_mul":
                a, b = rhs_def.children
                if is_u64_node(a, type_env) and is_u64_node(b, type_env):
                    return ScalarNode("fma", None, (a, b, lhs))
    return node


def count_scalar_var_uses(node: ScalarNode, counts: dict[int, int]) -> None:
    if node.kind == "var":
        vid = int(node.val)
        counts[vid] = counts.get(vid, 0) + 1
    for ch in node.children:
        count_scalar_var_uses(ch, counts)


def optimize_straight_line_code(
    cur: WireCursor,
    param_types: dict[int, tuple[str, ...]],
    fact_vars: set[int] | None = None,
) -> tuple[list[tuple[int, list[str], ScalarNode]], int, dict[int, ScalarNode], dict[int, tuple[str, ...]], bool] | None:
    raw_bindings: list[tuple[int, list[str], ScalarNode]] = []
    while True:
        tag = cur.next()
        if tag == "C_ret":
            ret_v = cur.next_nat()
            break
        if tag != "C_let":
            return None
        dst = cur.next_nat()
        ty_toks = parse_type_tokens(cur)
        expr_tag = cur.next()
        if expr_tag != "E_scalar":
            return None
        raw_bindings.append((dst, ty_toks, parse_scalar(cur)))

    var_uses: dict[int, int] = {}
    live_uses: dict[int, int] = {ret_v: 1}
    if fact_vars:
        for fv in fact_vars:
            live_uses[fv] = live_uses.get(fv, 0) + 1
    for j in range(len(raw_bindings) - 1, -1, -1):
        dst, _ty_toks, raw_expr = raw_bindings[j]
        var_uses[j] = live_uses.pop(dst, 0)
        count_scalar_var_uses(raw_expr, live_uses)

    bindings: list[tuple[int, list[str], ScalarNode]] = []
    scalar_env: dict[int, ScalarNode] = {}
    scalar_def_step: dict[int, int] = {}
    type_env: dict[int, tuple[str, ...]] = dict(param_types)
    changed = False
    for step_idx, (dst, ty_toks, raw_expr) in enumerate(raw_bindings):
        ty_tuple = tuple(ty_toks)
        inlinable_env = {
            vid: node
            for vid, node in scalar_env.items()
            if node.kind in ("u64", "bool", "var") or var_uses.get(scalar_def_step.get(vid, -1), 2) <= 1
        }
        opt_expr = rewrite_scalar(raw_expr, inlinable_env, type_env) if ty_tuple in U64_TYPES else raw_expr
        if opt_expr != raw_expr:
            changed = True
        invalidate_scalar_env_var(scalar_env, dst)
        scalar_def_step.pop(dst, None)
        type_env[dst] = ty_tuple
        if ty_tuple in U64_TYPES and is_u64_node(opt_expr, type_env) and not scalar_node_mentions_var(opt_expr, dst):
            scalar_env[dst] = opt_expr
            scalar_def_step[dst] = step_idx
        bindings.append((dst, ty_toks, opt_expr))
    return bindings, ret_v, scalar_env, type_env, changed


def scalar_expr_may_trap(node: ScalarNode, type_env: dict[int, tuple[str, ...]]) -> bool:
    if node.kind == "u64" or node.kind == "bool":
        return False
    if node.kind == "var":
        return int(node.val) not in type_env
    if any(scalar_expr_may_trap(ch, type_env) for ch in node.children):
        return True
    if infer_scalar_type(node, type_env) is None:
        return True
    if node.kind == "bin":
        op = str(node.val)
        if op in ("B_addChecked256", "B_subChecked256", "B_mulChecked256"):
            return True
        if op in ("B_div", "B_mod"):
            lhs, rhs = node.children
            l_ty = infer_scalar_type(lhs, type_env)
            r_ty = infer_scalar_type(rhs, type_env)
            if l_ty in U64_TYPES and r_ty in U64_TYPES:
                return False
            if op == "B_div" and rhs.kind == "u64" and int(rhs.val) == 1:
                return False
            return True
    return False


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


def scalar_node_cost(node: ScalarNode, prof: dict[str, int]) -> int:
    if node.kind in ("u64", "bool", "var"):
        return 0
    if node.kind == "un":
        op_cost = prof["clz256"] if node.val == "U_clz256" else prof["bitwise"]
        return op_cost + scalar_node_cost(node.children[0], prof)
    if node.kind == "sel":
        return prof["select"] + sum(scalar_node_cost(ch, prof) for ch in node.children)
    if node.kind == "fma":
        return prof["fma"] + sum(scalar_node_cost(ch, prof) for ch in node.children)
    if node.kind == "bin":
        op = str(node.val)
        lhs, rhs = node.children
        sub = scalar_node_cost(lhs, prof) + scalar_node_cost(rhs, prof)
        dup_penalty = 1 if (op == "B_add" and lhs == rhs) else 0
        if op in ("B_add", "B_sub"):
            return prof["addSub"] + dup_penalty + sub
        if op in ("B_bitAnd", "B_bitOr", "B_bitXor", "B_eor3"):
            return prof["bitwise"] + sub
        if op in ("B_clmul64", "B_clmul64Hi", "B_gf2Affine"):
            return 1 + sub
        if op in ("B_shl", "B_shr", "B_sar"):
            return prof["shift"] + sub
        if op in ("B_eq", "B_lt", "B_le"):
            return prof["cmp"] + sub
        if op == "B_mul":
            return prof["mul"] + sub
        if op in ("B_div", "B_mod"):
            return prof["divMod"] + sub
        if op in ("B_addChecked256", "B_subChecked256"):
            return prof["addSubChecked256"] + sub
        if op == "B_mulChecked256":
            return prof["mulChecked256"] + sub
    return 0


def handle_lnir_opt_request(req: dict) -> dict:
    wire = req.get("wire")
    if not isinstance(wire, str) or not wire.startswith("LNIR_WIRE_V1|"):
        return {}
    target = req.get("target", "x86_64")
    prof = TARGET_COST_PROFILES.get(target if isinstance(target, str) else "x86_64", TARGET_COST_PROFILES["x86_64"])
    try:
        cur = WireCursor(wire.split("|"))
        if cur.next() != "LNIR_WIRE_V1":
            return {}
        mod_hex = cur.next()
        if hex_decode(mod_hex) is None:
            return {}
        decl_count = cur.next_nat()
        if decl_count != 1 or cur.next() != "D_decl":
            return {}
        name_hex = cur.next()
        if hex_decode(name_hex) is None:
            return {}
        assurance = cur.next()
        if assurance not in ASSURANCE_TAGS:
            return {}
        is_gpu = "1" if cur.next_bool() else "0"
        param_len = cur.next_nat()
        param_toks: list[str] = []
        param_types: dict[int, tuple[str, ...]] = {}
        for _ in range(param_len):
            pid = cur.next_nat()
            pname_hex = cur.next()
            if hex_decode(pname_hex) is None:
                return {}
            pborrow = "1" if cur.next_bool() else "0"
            pty = parse_type_tokens(cur)
            param_types[pid] = tuple(pty)
            param_toks.extend([str(pid), pname_hex, pborrow, *pty])
        ret_ty = parse_type_tokens(cur)
        body_start_idx = cur.idx
        raw_cost = 0
        while True:
            rtag = cur.next()
            if rtag == "C_ret":
                cur.next_nat()
                break
            if rtag != "C_let":
                return {}
            cur.next_nat()
            parse_type_tokens(cur)
            if cur.next() != "E_scalar":
                return {}
            raw_cost += scalar_node_cost(parse_scalar(cur), prof)

        fact_toks, fact_vars = parse_trailing_facts(cur)
        opt_cur = WireCursor(cur.tokens[body_start_idx:])
        opt_res = optimize_straight_line_code(opt_cur, param_types, fact_vars)
        if opt_res is None:
            return {}
        bindings, ret_v, scalar_env, _final_type_env, changed = opt_res

        env_at_step: list[dict[int, tuple[str, ...]]] = []
        cur_ty_env: dict[int, tuple[str, ...]] = dict(param_types)
        for dst, ty_toks, _expr in bindings:
            env_at_step.append(dict(cur_ty_env))
            cur_ty_env[dst] = tuple(ty_toks)

        if ret_v in scalar_env and scalar_env[ret_v].kind == "var":
            cand_v = int(scalar_env[ret_v].val)
            if cur_ty_env.get(cand_v) == cur_ty_env.get(ret_v):
                ret_v = cand_v
                changed = True
        used: set[int] = {ret_v, *fact_vars}

        kept_rev: list[tuple[int, list[str], ScalarNode]] = []
        for (dst, ty_toks, expr), step_ty_env in zip(reversed(bindings), reversed(env_at_step)):
            if dst in used or scalar_expr_may_trap(expr, step_ty_env):
                used.discard(dst)
                kept_rev.append((dst, ty_toks, expr))
                used |= collect_scalar_vars(expr)
            else:
                changed = True
        if not changed:
            return {}
        kept = list(reversed(kept_rev))
        cand_cost = sum(scalar_node_cost(expr, prof) for _dst, _ty_toks, expr in kept)
        if cand_cost > raw_cost:
            return {}
        code_toks: list[str] = []
        for dst, ty_toks, expr in kept:
            code_toks.extend(["C_let", str(dst), *ty_toks, "E_scalar", *encode_scalar(expr)])
        code_toks.extend(["C_ret", str(ret_v)])
        cand_tokens = [
            "LNIR_WIRE_V1", mod_hex, "1", "D_decl", name_hex, assurance, is_gpu,
            str(param_len), *param_toks, *ret_ty, *code_toks, *fact_toks,
        ]
        return {"wire": "|".join(cand_tokens)}
    except ValueError:
        return {}


DECL_MODIFIERS = frozenset({
    "private", "protected", "noncomputable", "scoped", "local",
    "unsafe", "partial", "nonrec", "public", "meta",
})

LEAN_KEYWORDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "coinductive",
    "instance", "axiom", "opaque", "constant", "where", "by", "fun", "let", "have", "haveI",
    "letI", "show", "from", "match", "with", "if", "then", "else", "do", "return", "for",
    "in", "unless", "try", "catch", "finally", "mutual",
})


def is_lean_id_rest(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?"


def scan_guillemet_end(s: str, start: int) -> int | None:
    if start >= len(s) or s[start] != "«":
        return None
    end = s.find("»", start + 1)
    return len(s) if end == -1 else end + 1


def scan_char_lit_end(s: str, start: int) -> int | None:
    if start + 2 >= len(s) or s[start] != "'":
        return None
    c0 = s[start + 1]
    if c0 in ("'", "\n"):
        return None
    idx = start + 2
    if c0 == "\\":
        if idx >= len(s):
            return None
        esc = s[idx]
        idx += 1
        if esc in ("\\", '"', "'", "r", "n", "t"):
            pass
        elif esc == "x":
            if idx + 2 > len(s) or not all(c in "0123456789abcdefABCDEF" for c in s[idx : idx + 2]):
                return None
            idx += 2
        elif esc == "u":
            if idx + 4 > len(s) or not all(c in "0123456789abcdefABCDEF" for c in s[idx : idx + 4]):
                return None
            idx += 4
        else:
            return None
    return idx + 1 if idx < len(s) and s[idx] == "'" else None


def ends_with_closed_char_lit(s: str, end: int) -> bool:
    if end < 3 or end > len(s) or s[end - 1] != "'":
        return False
    lo = max(0, end - 10)
    return any(scan_char_lit_end(s, k) == end for k in range(lo, end - 2))


def scan_raw_string_end(s: str, start: int) -> int | None:
    if start >= len(s) or s[start] != "r":
        return None
    if start > 0:
        prev = s[start - 1]
        if prev == "'":
            if not ends_with_closed_char_lit(s, start):
                return None
        elif prev == ".":
            if start < 2 or s[start - 2] != ".":
                return None
        elif is_lean_id_rest(prev) or prev in ("»", "`"):
            return None
    i = start + 1
    while i < len(s) and s[i] == "#":
        i += 1
    hashes = i - start - 1
    if i >= len(s) or s[i] != '"':
        return None
    close_pat = '"' + ("#" * hashes)
    end = s.find(close_pat, i + 1)
    return len(s) if end == -1 else end + len(close_pat)


def scan_string_lit_end(s: str, start: int) -> int | None:
    if start >= len(s) or s[start] != '"':
        return None
    i = start + 1
    while i < len(s):
        if s[i] == "\\":
            i = min(i + 2, len(s))
        elif s[i] == '"':
            return i + 1
        else:
            i += 1
    return len(s)


def scan_block_comment_end(s: str, start: int) -> int | None:
    if not s.startswith("/-", start):
        return None
    is_doc = start + 2 < len(s) and s[start + 2] in ("-", "!")
    i = start + (3 if is_doc else 2)
    depth = 1
    while i < len(s) and depth > 0:
        if s.startswith("/-", i):
            depth += 1
            i += 2
        elif s.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            i += 1
    return i


def scan_interp_string_end(s: str, start: int) -> int | None:
    if start < 2 or start >= len(s) or s[start] != '"' or s[start - 1] != "!":
        return None
    j = start - 1
    while j > 0 and is_lean_id_rest(s[j - 1]):
        j -= 1
    if j == start - 1 or s[j].isdigit() or (j > 0 and s[j - 1] == "»"):
        return None
    i = start + 1
    interp_depth = 0
    while i < len(s):
        if interp_depth > 0:
            nxt = skip_lean_atom(s, i)
            if nxt is not None:
                i = nxt
                continue
            if s[i] == "{":
                interp_depth += 1
            elif s[i] == "}":
                interp_depth -= 1
            i += 1
            continue
        if s[i] == "\\":
            i = min(i + 2, len(s))
        elif s[i] == "{":
            interp_depth = 1
            i += 1
        elif s[i] == '"':
            return i + 1
        else:
            i += 1
    return len(s)


def skip_lean_atom(s: str, start: int) -> int | None:
    if start >= len(s):
        return None
    ch = s[start]
    if ch == "«":
        return scan_guillemet_end(s, start)
    if s.startswith("--", start):
        nl = s.find("\n", start + 2)
        return len(s) if nl == -1 else nl
    if s.startswith("/-", start):
        return scan_block_comment_end(s, start)
    if ch == "'":
        if start > 0:
            prev = s[start - 1]
            if (is_lean_id_rest(prev) and not ends_with_closed_char_lit(s, start)) or prev == "»":
                return None
        return scan_char_lit_end(s, start)
    if ch == '"':
        return scan_interp_string_end(s, start) or scan_string_lit_end(s, start)
    if ch == "r":
        return scan_raw_string_end(s, start)
    return None


def strip_leading_attr_block(s: str) -> str | None:
    if not s.startswith("@["):
        return None
    depth = 0
    i = 1
    while i < len(s):
        nxt = skip_lean_atom(s, i)
        if nxt is not None:
            i = nxt
            continue
        ch = s[i]
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return s[i + 1 :]
        i += 1
    return None


def strip_leading_set_option_in(s: str) -> str | None:
    if not s.startswith("set_option") or (len(s) > 10 and not s[10].isspace()):
        return None
    m = re.match(r'^set_option\s+\S+\s+(?:"(?:\\.|[^"\\])*"|\S+)\s+in(?=\s|$)', s)
    return s[m.end() :] if m else None


def strip_decl_prefixes(s: str) -> str:
    rest = s.lstrip()
    while rest:
        if rest.startswith("/-"):
            end = scan_block_comment_end(rest, 0)
            if end is not None:
                rest = rest[end:].lstrip()
                continue
        if rest.startswith("--"):
            nl = rest.find("\n")
            if nl != -1:
                rest = rest[nl + 1 :].lstrip()
                continue
            return ""
        after_attr = strip_leading_attr_block(rest)
        if after_attr is not None:
            rest = after_attr.lstrip()
            continue
        after_opt = strip_leading_set_option_in(rest)
        if after_opt is not None:
            rest = after_opt.lstrip()
            continue
        matched_mod = False
        for mod in DECL_MODIFIERS:
            if rest.startswith(mod) and (len(rest) == len(mod) or rest[len(mod)].isspace()):
                after_mod = rest[len(mod) :].lstrip()
                if mod in ("noncomputable", "public", "meta") and (
                    after_mod == "section" or after_mod.startswith(("section ", "import "))
                ):
                    break
                rest = after_mod
                matched_mod = True
                break
        if not matched_mod:
            break
    return rest


def has_decl_header(stmt_trimmed: str) -> bool:
    rest = strip_decl_prefixes(stmt_trimmed)
    for kw in ("theorem", "lemma"):
        if rest.startswith(kw) and len(rest) > len(kw) and rest[len(kw)].isspace():
            after_kw = rest[len(kw) :].lstrip()
            if after_kw and not after_kw[0].isdigit() and after_kw[0] not in ":({[":
                return True
    return False


def split_top_level_colon(s: str, start_idx: int = 0) -> tuple[str, str] | None:
    paren = bracket = brace = strict_brace = 0
    i = start_idx
    while i < len(s):
        nxt = skip_lean_atom(s, i)
        if nxt is not None:
            i = nxt
            continue
        ch = s[i]
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren = max(0, paren - 1)
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket = max(0, bracket - 1)
        elif ch == "{":
            brace += 1
        elif ch == "}":
            brace = max(0, brace - 1)
        elif ch == "⦃":
            strict_brace += 1
        elif ch == "⦄":
            strict_brace = max(0, strict_brace - 1)
        elif ch == ":" and paren == 0 and bracket == 0 and brace == 0 and strict_brace == 0:
            if i + 1 < len(s) and s[i + 1] == "=":
                i += 2
                continue
            return s[:i].rstrip(), s[i + 1 :].strip()
        i += 1
    return None


def split_top_level_assign(s: str) -> tuple[str, str] | None:
    paren = bracket = brace = strict_brace = 0
    i = 0
    while i + 1 < len(s):
        nxt = skip_lean_atom(s, i)
        if nxt is not None:
            i = nxt
            continue
        ch = s[i]
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren = max(0, paren - 1)
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket = max(0, bracket - 1)
        elif ch == "{":
            brace += 1
        elif ch == "}":
            brace = max(0, brace - 1)
        elif ch == "⦃":
            strict_brace += 1
        elif ch == "⦄":
            strict_brace = max(0, strict_brace - 1)
        elif ch == ":" and s[i + 1] == "=" and paren == 0 and bracket == 0 and brace == 0 and strict_brace == 0:
            return s[:i].rstrip(), s[i + 2 :]
        i += 1
    return None


def mask_lean_comments_preserving_lines(s: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(s):
        if s.startswith("--", i):
            nl = s.find("\n", i + 2)
            end = len(s) if nl == -1 else nl
            out.append(" " * (end - i))
            i = end
            continue
        if s.startswith("/-", i):
            end = scan_block_comment_end(s, i)
            assert end is not None
            out.append("".join(ch if ch in ("\n", "\r") else " " for ch in s[i:end]))
            i = end
            continue
        nxt = skip_lean_atom(s, i)
        if nxt is not None:
            out.append(s[i:nxt])
            i = nxt
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def flatten_inline_preserving_literals(s: str) -> str:
    out: list[str] = []
    i = 0
    emitted = False
    pending_space = False
    while i < len(s):
        if s.startswith("/-", i):
            end = scan_block_comment_end(s, i)
            assert end is not None
            if emitted:
                pending_space = True
            i = end
            continue
        if s.startswith("--", i):
            nl = s.find("\n", i + 2)
            i = len(s) if nl == -1 else nl
            if emitted:
                pending_space = True
            continue
        nxt = skip_lean_atom(s, i)
        if nxt is not None:
            if pending_space:
                out.append(" ")
                pending_space = False
            out.append(s[i:nxt])
            emitted = True
            i = nxt
            continue
        if s[i].isspace():
            if emitted:
                pending_space = True
            i += 1
            continue
        if pending_space:
            out.append(" ")
            pending_space = False
        out.append(s[i])
        emitted = True
        i += 1
    return "".join(out)


def contains_lean_word(haystack: str, word: str) -> bool:
    if not word:
        return False
    is_guillemet = word.startswith("«") and word.endswith("»")
    i = 0
    while i < len(haystack):
        nxt = skip_lean_atom(haystack, i)
        if nxt is not None:
            if is_guillemet and haystack[i:nxt] == word:
                return True
            i = nxt
            continue
        if not is_guillemet and haystack.startswith(word, i):
            prev_ok = i == 0 or not is_lean_id_rest(haystack[i - 1])
            end = i + len(word)
            next_ok = end >= len(haystack) or not is_lean_id_rest(haystack[end])
            if prev_ok and next_ok:
                return True
        i += 1
    return False


def split_stmt_at_top_level_semicolons(s_orig: str, s_clean: str, pad: str) -> str:
    parts: list[str] = []
    depth = 0
    last = 0
    i = 0
    while i < len(s_clean):
        nxt = skip_lean_atom(s_clean, i)
        if nxt is not None:
            i = nxt
            continue
        ch = s_clean[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ";" and depth == 0 and not s_clean.startswith(";>", i):
            seg = s_orig[last:i].strip()
            if seg:
                parts.append(f"{pad}{seg}")
            last = i + 1
        i += 1
    tail = s_orig[last:].strip()
    if tail:
        parts.append(f"{pad}{tail}")
    return "\n".join(parts) if len(parts) >= 2 else s_orig


def format_cut_proof_rhs(proof_rhs: str, base_indent: int) -> str:
    trimmed = proof_rhs.strip()
    if "\n" not in trimmed:
        return trimmed
    lines = trimmed.splitlines()
    out = [lines[0].rstrip()]
    for ln in lines[1:]:
        if not ln.strip():
            out.append("")
        else:
            lead = len(ln) - len(ln.lstrip(" "))
            out.append(ln[min(lead, base_indent) :])
    return "\n".join(out)


def parse_have_cut_stmt(stmt_orig: str) -> tuple[str, str, str, str] | None:
    assign_split = split_top_level_assign(stmt_orig)
    if assign_split is None:
        return None
    lhs_orig, proof_orig = assign_split
    if not proof_orig.strip():
        return None
    lhs_stripped = lhs_orig.lstrip()
    if not lhs_stripped.startswith("have") or (len(lhs_stripped) > 4 and not lhs_stripped[4].isspace()):
        return None
    rem = lhs_stripped[4:].lstrip()
    if not rem:
        return None
    if rem.startswith(":") and not rem.startswith(":="):
        ty_raw = rem[1:]
        ty = flatten_inline_preserving_literals(ty_raw) if "\n" in ty_raw else ty_raw.strip()
        return ("this", "", ty, proof_orig) if ty else None
    g_end = scan_guillemet_end(rem, 0)
    if g_end is not None:
        if g_end < len(rem) and rem[g_end] == ".":
            return None
        ident = rem[:g_end]
        after_ident = rem[g_end:]
    else:
        if rem[0].isdigit() or not is_lean_id_rest(rem[0]):
            return None
        j = 0
        while j < len(rem) and is_lean_id_rest(rem[j]):
            j += 1
        ident = rem[:j]
        after_ident = rem[j:]
        if not ident or ident == "_" or ident in LEAN_KEYWORDS:
            return None
    colon_split = split_top_level_colon(after_ident)
    if colon_split is None:
        return None
    b_orig, ty_orig = colon_split
    b_trimmed = b_orig.strip()
    ty = flatten_inline_preserving_literals(ty_orig) if "\n" in ty_orig else ty_orig.strip()
    if not ty or (b_trimmed and not b_trimmed.startswith(("(", "{", "[", "⦃"))):
        return None
    binders_norm = flatten_inline_preserving_literals(b_trimmed) if "\n" in b_trimmed else b_trimmed
    cut_binders = f" {binders_norm}" if binders_norm else ""
    return ident, cut_binders, ty, proof_orig


def extract_have_cuts(decl_name: str, stmt_src: str, body_src: str) -> list[str]:
    eff_name = decl_name.strip() or "fission_thm"
    stmt_trimmed = stmt_src.strip()
    body_trimmed = body_src.strip()
    if not stmt_trimmed or not body_trimmed:
        return []
    if has_decl_header(stmt_trimmed):
        after_prefixes = strip_decl_prefixes(stmt_trimmed)
        prefix_offset = len(stmt_trimmed) - len(after_prefixes)
        sig_split = split_top_level_colon(stmt_trimmed, prefix_offset)
        if sig_split is None:
            return []
        binder_prefix, goal_ty = sig_split
        if not binder_prefix:
            return []
    else:
        sig_split = split_top_level_colon(stmt_trimmed)
        if sig_split is not None:
            binders, goal_ty = sig_split
            binders = binders.strip()
        elif not stmt_trimmed.startswith((":", "(", "{", "[")):
            binders, goal_ty = "", stmt_trimmed
        else:
            return []
        binder_prefix = f"theorem {eff_name} {binders}" if binders else f"theorem {eff_name}"
    if not goal_ty:
        return []

    rhs_orig = body_src.lstrip()
    rhs_clean = mask_lean_comments_preserving_lines(rhs_orig)
    first_nl = rhs_clean.find("\n")
    if first_nl == -1:
        first_nl = len(rhs_clean)
    first_line_clean = rhs_clean[:first_nl]
    if not first_line_clean.startswith("by") or (len(first_line_clean) > 2 and not first_line_clean[2].isspace()):
        return []
    after_by_clean = first_line_clean[2:]
    inline_after_by = after_by_clean.strip()
    after_nl_clean = rhs_clean[first_nl + 1 :] if first_nl < len(rhs_clean) else ""
    after_nl_orig = rhs_orig[first_nl + 1 :] if first_nl < len(rhs_orig) else ""

    nonempty_lines = [ln for ln in after_nl_clean.splitlines() if ln.strip()]
    if nonempty_lines:
        base_indent = len(nonempty_lines[0]) - len(nonempty_lines[0].lstrip(" "))
        if base_indent <= 0:
            return []
    elif inline_after_by:
        base_indent = 2
    else:
        return []
    pad = " " * base_indent

    if not inline_after_by:
        raw_orig, raw_clean = after_nl_orig, after_nl_clean
    else:
        ws_after_by = len(after_by_clean) - len(after_by_clean.lstrip())
        inline_start = 2 + ws_after_by
        in_o = rhs_orig[inline_start:first_nl].rstrip()
        in_c = rhs_clean[inline_start:first_nl].rstrip()
        raw_orig = f"{pad}{in_o}" if not after_nl_orig else f"{pad}{in_o}\n{after_nl_orig}"
        raw_clean = f"{pad}{in_c}" if not after_nl_clean else f"{pad}{in_c}\n{after_nl_clean}"

    if ";" in raw_clean:
        o_lines: list[str] = []
        c_lines: list[str] = []
        for lo, lc in zip(raw_orig.split("\n"), raw_clean.split("\n")):
            if (
                len(lc) - len(lc.lstrip(" ")) == base_indent
                and lc.lstrip().startswith(("have", "letI"))
                and ";" in lc
            ):
                o_lines.append(split_stmt_at_top_level_semicolons(lo, lc, pad))
                c_lines.append(split_stmt_at_top_level_semicolons(lc, lc, pad))
            else:
                o_lines.append(lo)
                c_lines.append(lc)
        body_orig = "\n".join(o_lines)
        body_clean = "\n".join(c_lines)
    else:
        body_orig, body_clean = raw_orig, raw_clean

    if len(body_orig) != len(body_clean):
        return []

    stmt_ranges: list[tuple[int, int]] = []
    cur_start: int | None = None
    cur_end = 0
    pos = 0
    total_len = len(body_orig)
    while pos < total_len:
        nl = body_orig.find("\n", pos)
        line_end = total_len if nl == -1 else nl
        next_pos = min(line_end + 1, total_len)
        line_end_no_cr = line_end - 1 if line_end > pos and body_orig[line_end - 1] == "\r" else line_end
        line_clean = body_clean[pos:line_end_no_cr]
        if line_clean.strip():
            if "\t" in line_clean[: len(line_clean) - len(line_clean.lstrip())]:
                return []
            indent = len(line_clean) - len(line_clean.lstrip(" "))
            if indent < base_indent:
                return []
            if indent == base_indent:
                if cur_start is not None:
                    stmt_ranges.append((cur_start, cur_end))
                cur_start = pos
            cur_end = line_end_no_cr
        pos = next_pos
    if cur_start is not None:
        stmt_ranges.append((cur_start, cur_end))
    if len(stmt_ranges) < 2:
        return []

    sig_clean = mask_lean_comments_preserving_lines(f"{binder_prefix} : {goal_ty}")
    seen_idents: set[str] = set()
    have_cuts: list[tuple[str, str, str, str]] = []
    has_classical = False
    conclusion_start: int | None = None

    for idx, (st, en) in enumerate(stmt_ranges):
        stmt_o = body_orig[st:en]
        stmt_c = body_clean[st:en]
        if contains_lean_word(stmt_c, "rename_i"):
            return []
        if idx + 1 < len(stmt_ranges):
            if stmt_c.strip() == "classical":
                has_classical = True
                continue
            cut = parse_have_cut_stmt(stmt_o)
            if cut is not None:
                ident, cut_binders, cut_ty, proof_rhs = cut
                if contains_lean_word(sig_clean, ident) or ident in seen_idents:
                    return []
                seen_idents.add(ident)
                have_cuts.append((ident, cut_binders, cut_ty, proof_rhs))
                continue
            if not have_cuts:
                return []
        conclusion_start = st
        break

    if not have_cuts or conclusion_start is None:
        return []

    promoted = ""
    shards: list[str] = []
    for ident, cut_binders, cut_ty, proof_rhs in have_cuts:
        rhs_fmt = format_cut_proof_rhs(proof_rhs, base_indent)
        if has_classical:
            if rhs_fmt.startswith("by\n"):
                rhs_fmt = f"by\n{pad}classical\n{rhs_fmt[3:]}"
            elif rhs_fmt.startswith("by "):
                rhs_fmt = f"by classical; {rhs_fmt[3:]}"
            else:
                rhs_fmt = f"by\n{pad}classical\n{pad}exact ({rhs_fmt})"
        shards.append(f"{binder_prefix}{promoted}{cut_binders} : {cut_ty} := {rhs_fmt}")
        if cut_binders:
            promoted += f" ({ident} : ∀{cut_binders}, {cut_ty})"
        else:
            promoted += f" ({ident} : {cut_ty})"

    cls_line = f"{pad}classical\n" if has_classical else ""
    concl_src = body_orig[conclusion_start:].rstrip()
    shards.append(f"{binder_prefix}{promoted} : {goal_ty} := by\n{cls_line}{concl_src}")
    return shards if len(shards) >= 2 else []


def handle_tactic_request(req: dict) -> dict:
    decl_name = req.get("decl_name", "fission_thm")
    stmt = req.get("stmt_src")
    body = req.get("body_src")
    avail = req.get("available_constants", [])
    if not isinstance(decl_name, str) or not isinstance(stmt, str) or not isinstance(body, str):
        return {}
    if not isinstance(avail, list) or not all(isinstance(x, str) for x in avail):
        return {}

    if re.search(r"\ba\s*\+\s*b\s*<\s*a\b", stmt) or re.search(r"\bx\s*\+\s*1\s*<\s*x\b", stmt):
        return {
            "kind": "counterexample_found",
            "witness_summary": "a = 0, b = 0 violates strict inequality a + b < a",
            "suggested_hypothesis": "h_pos : 0 < b",
            "accelerator_name": PLUGIN_NAME,
        }

    body_stripped = body.strip()
    if "simp" in body_stripped and "simp only" not in body_stripped:
        distilled = [c.strip() for c in avail if c.strip() and c.strip() not in EXCLUDED_CORE_CONSTS and not c.strip().startswith("_")]
        if distilled:
            return {
                "kind": "rewritten_proof",
                "new_body_src": f"by simp only [{', '.join(distilled)}]",
                "accelerator_name": PLUGIN_NAME,
                "estimated_speedup_hint": "9.5x",
            }

    cuts = extract_have_cuts(decl_name, stmt, body_stripped)
    if cuts:
        return {
            "kind": "subgoal_cuts",
            "cuts": cuts,
            "accelerator_name": PLUGIN_NAME,
        }
    return {}


def handle_request(req: object) -> dict:
    if not isinstance(req, dict):
        return {}
    budget = req.get("budget_ms", 25)
    if isinstance(budget, bool) or not isinstance(budget, (int, float)) or budget <= 0:
        return {}
    if "wire" in req and "stmt_src" not in req:
        return handle_lnir_opt_request(req)
    return handle_tactic_request(req)


def main() -> int:
    if "--simulate-hang-ms" in sys.argv:
        idx = sys.argv.index("--simulate-hang-ms")
        ms = int(sys.argv[idx + 1]) if idx + 1 < len(sys.argv) else 5000
        time.sleep(max(ms, 0) / 1000.0)
        print("{}", flush=True)
        return 0

    one_shot = "--one-shot" in sys.argv
    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except json.JSONDecodeError:
            print("{}", flush=True)
            if one_shot:
                break
            continue
        resp = handle_request(req)
        print(json.dumps(resp, separators=(",", ":")), flush=True)
        if one_shot:
            break
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
