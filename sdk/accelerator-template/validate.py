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

BOUNDARY_U64 = (
    0, 1, 2, 3, 7, 15, 31, 32, 63, 64,
    (1 << 31) - 1, 1 << 31, (1 << 32) - 1, 1 << 32,
    (1 << 63) - 1, 1 << 63, MASK64 - 1, MASK64,
)

TARGET_COST_PROFILES: dict[str, dict[str, int]] = {
    "x86_64": {"addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 4, "divMod": 24, "fma": 3, "select": 2},
    "arm64": {"addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 4, "divMod": 24, "fma": 2, "select": 2},
    "cuda_ptx": {"addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 5, "divMod": 36, "fma": 2, "select": 2},
    "apple_metal": {"addSub": 1, "bitwise": 1, "shift": 1, "cmp": 1, "mul": 5, "divMod": 36, "fma": 2, "select": 2},
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
        if not isinstance(cuts, list) or not cuts or not all(isinstance(c, str) and c.strip() for c in cuts):
            raise ValueError("subgoal_cuts.cuts must be a non-empty list of non-empty strings")
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


def parse_single_decl_wire(wire: str) -> ParsedDecl:
    cur = Cursor(wire.strip().split("|"))
    if cur.next() != "LNIR_WIRE_V1":
        raise ValueError("missing LNIR_WIRE_V1 header")
    mod_name = cur.next_hex()
    if cur.next_nat() != 1 or cur.next() != "D_decl":
        raise ValueError("expected single-declaration LNIRModule")
    name = cur.next_hex()
    assurance = cur.next()
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
    if cur.i != len(cur.toks):
        if cur.toks[cur.i] != "F_facts":
            raise ValueError(f"unexpected trailing wire tokens: {cur.toks[cur.i:]}")
    return ParsedDecl(mod_name, name, assurance, is_gpu, params, ret_ty, lets, ret_var)


def eval_scalar_ast(node: ScalarAst, env: dict[int, int]) -> int:
    if node.kind == "u64":
        return int(node.val) & MASK64
    if node.kind == "bool":
        return 1 if node.val else 0
    if node.kind == "var":
        idx = int(node.val)
        if idx not in env:
            raise ValueError(f"unbound SSA variable %{idx}")
        return env[idx]
    if node.kind == "un":
        v = eval_scalar_ast(node.args[0], env)
        if node.val == "U_not":
            return (~v) & MASK64
        if node.val == "U_neg":
            return (-v) & MASK64
        raise ValueError(f"unsupported UnaryOp {node.val!r}")
    if node.kind == "sel":
        c = eval_scalar_ast(node.args[0], env)
        return eval_scalar_ast(node.args[1] if c != 0 else node.args[2], env)
    if node.kind == "fma":
        a = eval_scalar_ast(node.args[0], env)
        b = eval_scalar_ast(node.args[1], env)
        c = eval_scalar_ast(node.args[2], env)
        return ((a * b) + c) & MASK64
    if node.kind == "bin":
        l = eval_scalar_ast(node.args[0], env)
        r = eval_scalar_ast(node.args[1], env)
        op = node.val
        if op == "B_add":
            return (l + r) & MASK64
        if op == "B_sub":
            return (l - r) & MASK64
        if op == "B_mul":
            return (l * r) & MASK64
        if op == "B_div":
            return 0 if r == 0 else (l // r) & MASK64
        if op == "B_mod":
            return 0 if r == 0 else (l % r) & MASK64
        if op == "B_bitAnd":
            return l & r
        if op == "B_bitOr":
            return l | r
        if op == "B_bitXor":
            return l ^ r
        if op == "B_shl":
            return (l << (r & 63)) & MASK64
        if op == "B_shr":
            return (l >> (r & 63)) & MASK64
        if op == "B_eq":
            return 1 if l == r else 0
        if op == "B_lt":
            return 1 if l < r else 0
        if op == "B_le":
            return 1 if l <= r else 0
    raise ValueError(f"unsupported ScalarAst node: {node}")


def eval_decl_u64(decl: ParsedDecl, args: list[int]) -> int:
    env = {pid: (val & MASK64) for (pid, _n, _b, _t), val in zip(decl.params, args)}
    for dst, _ty, expr in decl.lets:
        env[dst] = eval_scalar_ast(expr, env)
    if decl.ret_var not in env:
        raise ValueError(f"unbound return variable %{decl.ret_var}")
    return env[decl.ret_var]


def scalar_expr_cost(node: ScalarAst, profile: dict[str, int]) -> int:
    if node.kind in ("u64", "bool", "var"):
        return 0
    if node.kind == "un":
        return 1 + scalar_expr_cost(node.args[0], profile)
    if node.kind == "sel":
        return profile["select"] + sum(scalar_expr_cost(a, profile) for a in node.args)
    if node.kind == "fma":
        return profile["fma"] + sum(scalar_expr_cost(a, profile) for a in node.args)
    if node.kind == "bin":
        op = str(node.val)
        sub = scalar_expr_cost(node.args[0], profile) + scalar_expr_cost(node.args[1], profile)
        if op in ("B_add", "B_sub"):
            return profile["addSub"] + sub
        if op in ("B_bitAnd", "B_bitOr", "B_bitXor"):
            return profile["bitwise"] + sub
        if op in ("B_shl", "B_shr", "B_sar"):
            return profile["shift"] + sub
        if op in ("B_eq", "B_lt", "B_le"):
            return profile["cmp"] + sub
        if op == "B_mul":
            return profile["mul"] + sub
        if op in ("B_div", "B_mod"):
            return profile["divMod"] + sub
    return 4


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


def verify_opt_plugin_gate_64(src: ParsedDecl, cand: ParsedDecl, target: str) -> tuple[int, int]:
    src_sig = [(pid, pty) for pid, _n, _b, pty in src.params]
    cand_sig = [(pid, pty) for pid, _n, _b, pty in cand.params]
    if src_sig != cand_sig or src.ret_ty != cand.ret_ty:
        raise ValueError(f"Signature mismatch: {(src_sig, src.ret_ty)} != {(cand_sig, cand.ret_ty)}")
    arity = len(src.params)
    for state_idx in range(64):
        vec: list[int] = []
        for p_idx in range(arity):
            if state_idx < len(BOUNDARY_U64):
                vec.append(BOUNDARY_U64[(state_idx + p_idx * 5) % len(BOUNDARY_U64)])
            else:
                vec.append(splitmix64(state_idx * 131 + p_idx * 17 + 1))
        v_src = eval_decl_u64(src, vec)
        v_cand = eval_decl_u64(cand, vec)
        if v_src != v_cand:
            raise ValueError(f"64-state equivalence mismatch on {vec}: src={v_src} != cand={v_cand}")
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
        stderr=subprocess.DEVNULL,
        text=True,
    )
    try:
        out, _ = proc.communicate(payload, timeout=max(timeout_ms, 1) / 1000.0)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        return None, True
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
        lines = (FIXTURES_DIR / "tactic_requests.jsonl").read_text(encoding="utf-8").splitlines()
        seen_kinds: set[str] = set()
        saw_abstain = False
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
        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            self.assertEqual(seen_kinds, {"rewritten_proof", "counterexample_found", "subgoal_cuts"})
            self.assertTrue(saw_abstain)

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

        # Verify our gate itself kills an unsound ALU corruption mutant (B_add -> B_sub).
        sample_req = json.loads(lines[0])
        src_sample = parse_single_decl_wire(sample_req["wire"])
        corrupt_wire = sample_req["wire"].replace("|B_mul|", "|B_sub|", 1)
        corrupt_decl = parse_single_decl_wire(corrupt_wire)
        with self.assertRaises(ValueError):
            verify_opt_plugin_gate_64(src_sample, corrupt_decl, "x86_64")

    def test_04_malformed_and_adversarial_inputs_fail_safe(self) -> None:
        adv_lines = [
            ln for ln in (FIXTURES_DIR / "adversarial_requests.jsonl").read_text(encoding="utf-8").splitlines()
            if ln.strip()
        ]
        if self.plugin_cmd == [sys.executable, str(DEFAULT_PLUGIN)]:
            proc = subprocess.Popen(
                self.plugin_cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            out, _err = proc.communicate("\n".join(adv_lines) + "\n", timeout=3.0)
            self.assertEqual(proc.returncode, 0)
            resp_lines = [ln for ln in out.splitlines() if ln.strip()]
            self.assertEqual(len(resp_lines), len(adv_lines))
            for ln in resp_lines:
                self.assertIsNone(validate_tactic_certificate(ln))
        else:
            for ln in adv_lines:
                out_line, timed_out = run_single_stdio_request(self.plugin_cmd, ln, timeout_ms=500)
                self.assertFalse(timed_out)
                if out_line:
                    self.assertIsNone(validate_tactic_certificate(out_line))

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
