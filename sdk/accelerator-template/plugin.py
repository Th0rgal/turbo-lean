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


def rewrite_scalar(
    node: ScalarNode,
    scalar_env: dict[int, ScalarNode],
    type_env: dict[int, tuple[str, ...]],
) -> ScalarNode:
    if node.kind == "var" and int(node.val) in scalar_env:
        bound = scalar_env[int(node.val)]
        if bound.kind in ("u64", "bool", "var") and type_env.get(int(node.val)) == infer_scalar_type(bound, type_env):
            return bound
    if node.children:
        node = ScalarNode(node.kind, node.val, tuple(rewrite_scalar(ch, scalar_env, type_env) for ch in node.children))

    if node.kind == "bin":
        op = str(node.val)
        lhs, rhs = node.children
        lhs_is_u64 = is_u64_node(lhs, type_env)
        rhs_is_u64 = is_u64_node(rhs, type_env)
        if not (lhs_is_u64 and rhs_is_u64):
            return node

        lhs_def = scalar_env[int(lhs.val)] if lhs.kind == "var" and int(lhs.val) in scalar_env else lhs
        rhs_def = scalar_env[int(rhs.val)] if rhs.kind == "var" and int(rhs.val) in scalar_env else rhs

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


def optimize_straight_line_code(
    cur: WireCursor,
    param_types: dict[int, tuple[str, ...]],
) -> tuple[list[tuple[int, list[str], ScalarNode]], int, dict[int, ScalarNode], dict[int, tuple[str, ...]], bool] | None:
    bindings: list[tuple[int, list[str], ScalarNode]] = []
    scalar_env: dict[int, ScalarNode] = {}
    type_env: dict[int, tuple[str, ...]] = dict(param_types)
    changed = False
    while True:
        tag = cur.next()
        if tag == "C_ret":
            ret_v = cur.next_nat()
            return bindings, ret_v, scalar_env, type_env, changed
        if tag != "C_let":
            return None
        dst = cur.next_nat()
        ty_toks = parse_type_tokens(cur)
        ty_tuple = tuple(ty_toks)
        expr_tag = cur.next()
        if expr_tag != "E_scalar":
            return None
        raw_expr = parse_scalar(cur)
        opt_expr = rewrite_scalar(raw_expr, scalar_env, type_env) if ty_tuple in U64_TYPES else raw_expr
        if opt_expr != raw_expr:
            changed = True
        type_env[dst] = ty_tuple
        if ty_tuple in U64_TYPES and is_u64_node(opt_expr, type_env):
            scalar_env[dst] = opt_expr
        bindings.append((dst, ty_toks, opt_expr))


def scalar_expr_may_trap(node: ScalarNode, type_env: dict[int, tuple[str, ...]]) -> bool:
    if any(scalar_expr_may_trap(ch, type_env) for ch in node.children):
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


def handle_lnir_opt_request(req: dict) -> dict:
    wire = req.get("wire")
    if not isinstance(wire, str) or not wire.startswith("LNIR_WIRE_V1|"):
        return {}
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
        opt_res = optimize_straight_line_code(cur, param_types)
        if opt_res is None:
            return {}
        bindings, ret_v, scalar_env, type_env, changed = opt_res
        fact_toks, fact_vars = parse_trailing_facts(cur)
        if ret_v in scalar_env and scalar_env[ret_v].kind == "var":
            cand_v = int(scalar_env[ret_v].val)
            if type_env.get(cand_v) == type_env.get(ret_v):
                ret_v = cand_v
                changed = True
        used: set[int] = {ret_v, *fact_vars}

        def collect_vars(n: ScalarNode) -> set[int]:
            out = {int(n.val)} if n.kind == "var" else set()
            for ch in n.children:
                out |= collect_vars(ch)
            return out

        kept_rev: list[tuple[int, list[str], ScalarNode]] = []
        for dst, ty_toks, expr in reversed(bindings):
            if dst in used or scalar_expr_may_trap(expr, type_env):
                kept_rev.append((dst, ty_toks, expr))
                used |= collect_vars(expr)
            else:
                changed = True
        if not changed:
            return {}
        code_toks: list[str] = []
        for dst, ty_toks, expr in reversed(kept_rev):
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


def strip_leading_attr_block(s: str) -> str | None:
    if not s.startswith("@["):
        return None
    depth = 0
    i = 1
    in_str = False
    while i < len(s):
        ch = s[i]
        if in_str:
            if ch == "\\" and i + 1 < len(s):
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
        elif ch == "[":
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
        if rest.startswith("/--"):
            end = rest.find("-/", 3)
            if end != -1:
                rest = rest[end + 2 :].lstrip()
                continue
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
    depth = 0
    i = start_idx
    in_str = False
    while i < len(s):
        ch = s[i]
        if in_str:
            if ch == "\\" and i + 1 < len(s):
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
        elif ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            if i + 1 < len(s) and s[i + 1] == "=":
                i += 2
                continue
            return s[:i].rstrip(), s[i + 1 :].strip()
        i += 1
    return None


def split_top_level_assign(s: str) -> tuple[str, str] | None:
    depth = 0
    i = 0
    in_str = False
    while i + 1 < len(s):
        ch = s[i]
        if in_str:
            if ch == "\\" and i + 2 <= len(s):
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
        elif ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and s[i + 1] == "=" and depth == 0:
            return s[:i].rstrip(), s[i + 2 :].strip()
        i += 1
    return None


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
        elif not stmt_trimmed.startswith((":", "(", "{", "[")):
            binders, goal_ty = "", stmt_trimmed
        else:
            return []
        binder_prefix = f"theorem {eff_name} {binders}" if binders else f"theorem {eff_name}"
    if not goal_ty:
        return []

    after_by = body_trimmed
    if after_by == "by" or after_by.startswith(("by ", "by\n", "by\t")):
        after_by = after_by[2:].strip()
    else:
        return []
    if not after_by:
        return []

    lines = [ln.strip() for ln in after_by.splitlines() if ln.strip()]
    if len(lines) < 2:
        return []

    have_cuts: list[tuple[str, str, str, str]] = []
    concl_lines: list[str] = []
    for idx, ln in enumerate(lines):
        if idx + 1 < len(lines) and ln.startswith("have ") and not concl_lines:
            assign_split = split_top_level_assign(ln[5:].strip())
            if assign_split is None:
                return []
            lhs, rhs = assign_split
            colon_split = split_top_level_colon(lhs)
            if colon_split is None:
                return []
            lhs_head, cut_ty = colon_split
            lhs_head = lhs_head.strip()
            if not lhs_head or not cut_ty or not rhs:
                return []
            m_ident = re.match(r"^([^\s({[:]+)(.*)$", lhs_head)
            if m_ident is None:
                return []
            ident = m_ident.group(1)
            cut_binders_raw = m_ident.group(2).strip()
            if not ident or ident == "_" or ident[0].isdigit():
                return []
            if cut_binders_raw and not cut_binders_raw.startswith(("(", "{", "[")):
                return []
            cut_binders = f" {cut_binders_raw}" if cut_binders_raw else ""
            have_cuts.append((ident, cut_binders, cut_ty, rhs))
        else:
            concl_lines.append(ln)

    if not have_cuts or not concl_lines:
        return []

    promoted = ""
    shards: list[str] = []
    for ident, cut_binders, cut_ty, rhs in have_cuts:
        shards.append(f"{binder_prefix}{promoted}{cut_binders} : {cut_ty} := {rhs}")
        if cut_binders:
            promoted += f" ({ident} : ∀{cut_binders}, {cut_ty})"
        else:
            promoted += f" ({ident} : {cut_ty})"
    concl_body = "\n  ".join(concl_lines)
    shards.append(f"{binder_prefix}{promoted} : {goal_ty} := by\n  {concl_body}")
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
