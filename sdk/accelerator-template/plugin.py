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


def rewrite_scalar(node: ScalarNode, scalar_env: dict[int, ScalarNode]) -> ScalarNode:
    if node.kind == "var" and int(node.val) in scalar_env:
        bound = scalar_env[int(node.val)]
        if bound.kind in ("u64", "bool", "var"):
            return bound
    if node.children:
        node = ScalarNode(node.kind, node.val, tuple(rewrite_scalar(ch, scalar_env) for ch in node.children))

    if node.kind == "bin":
        op = str(node.val)
        lhs, rhs = node.children
        if lhs.kind == "var" and int(lhs.val) in scalar_env:
            lhs_def = scalar_env[int(lhs.val)]
        else:
            lhs_def = lhs
        if rhs.kind == "var" and int(rhs.val) in scalar_env:
            rhs_def = scalar_env[int(rhs.val)]
        else:
            rhs_def = rhs

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
                return ScalarNode("fma", None, (a, b, rhs))
            if rhs_def.kind == "bin" and rhs_def.val == "B_mul":
                a, b = rhs_def.children
                return ScalarNode("fma", None, (a, b, lhs))
    return node


def optimize_straight_line_code(cur: WireCursor) -> tuple[list[str], bool] | None:
    bindings: list[tuple[int, list[str], ScalarNode]] = []
    scalar_env: dict[int, ScalarNode] = {}
    changed = False
    while True:
        tag = cur.next()
        if tag == "C_ret":
            ret_v = cur.next_nat()
            if ret_v in scalar_env and scalar_env[ret_v].kind == "var":
                ret_v = int(scalar_env[ret_v].val)
                changed = True
            used: set[int] = {ret_v}

            def collect_vars(n: ScalarNode) -> set[int]:
                out = {int(n.val)} if n.kind == "var" else set()
                for ch in n.children:
                    out |= collect_vars(ch)
                return out

            kept_rev: list[tuple[int, list[str], ScalarNode]] = []
            for dst, ty_toks, expr in reversed(bindings):
                if dst in used:
                    kept_rev.append((dst, ty_toks, expr))
                    used |= collect_vars(expr)
                else:
                    changed = True
            out_toks: list[str] = []
            for dst, ty_toks, expr in reversed(kept_rev):
                out_toks.extend(["C_let", str(dst), *ty_toks, "E_scalar", *encode_scalar(expr)])
            out_toks.extend(["C_ret", str(ret_v)])
            return out_toks, changed
        if tag != "C_let":
            return None
        dst = cur.next_nat()
        ty_toks = parse_type_tokens(cur)
        expr_tag = cur.next()
        if expr_tag != "E_scalar":
            return None
        raw_expr = parse_scalar(cur)
        opt_expr = rewrite_scalar(raw_expr, scalar_env)
        if opt_expr != raw_expr:
            changed = True
        scalar_env[dst] = opt_expr
        bindings.append((dst, ty_toks, opt_expr))


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
        for _ in range(param_len):
            pid = cur.next_nat()
            pname_hex = cur.next()
            if hex_decode(pname_hex) is None:
                return {}
            pborrow = "1" if cur.next_bool() else "0"
            pty = parse_type_tokens(cur)
            param_toks.extend([str(pid), pname_hex, pborrow, *pty])
        ret_ty = parse_type_tokens(cur)
        opt_res = optimize_straight_line_code(cur)
        if opt_res is None:
            return {}
        code_toks, changed = opt_res
        fact_toks = cur.tokens[cur.idx:]
        if fact_toks and fact_toks[0] != "F_facts":
            return {}
        if not changed:
            return {}
        cand_tokens = [
            "LNIR_WIRE_V1", mod_hex, "1", "D_decl", name_hex, assurance, is_gpu,
            str(param_len), *param_toks, *ret_ty, *code_toks, *fact_toks,
        ]
        return {"wire": "|".join(cand_tokens)}
    except ValueError:
        return {}


def extract_have_cuts(body_src: str) -> list[str]:
    cuts: list[str] = []
    for line in body_src.splitlines():
        s = line.strip()
        if s.startswith("have ") and ":=" in s:
            cuts.append(s)
        elif s.startswith("exact ") and cuts:
            cuts.append(s)
    return cuts if len(cuts) >= 3 else []


def handle_tactic_request(req: dict) -> dict:
    stmt = req.get("stmt_src")
    body = req.get("body_src")
    avail = req.get("available_constants", [])
    if not isinstance(stmt, str) or not isinstance(body, str):
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

    cuts = extract_have_cuts(body_stripped)
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
    if isinstance(budget, (int, float)) and budget <= 0:
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

    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except json.JSONDecodeError:
            print("{}", flush=True)
            continue
        resp = handle_request(req)
        print(json.dumps(resp, separators=(",", ":")), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
