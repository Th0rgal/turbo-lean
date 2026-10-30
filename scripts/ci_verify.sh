#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="$ROOT_DIR/target/release:$PATH:$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$HOME/.elan/bin:$HOME/.cargo/bin"

TURBO_BIN="${TURBO_AUDITOR_BIN:-$ROOT_DIR/target/release/turbo-lean}"
if [ ! -x "$TURBO_BIN" ]; then
  echo "[FAIL] Missing turbo-lean auditor: $TURBO_BIN" >&2
  exit 1
fi

echo "[1/3] Checking doc & context ratchet (--sync-docs)..."
python3 "$ROOT_DIR/scripts/sync_docs_inventory.py" --check

echo "[2/3] Auditing TurboLean/Spec.lean & LeanNative/Spec.lean via turbo-lean audit-spec..."
if [ -x "$TURBO_BIN" ]; then
  "$TURBO_BIN" --json audit-spec lean/TurboLean/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==d['total_specs_audited'] and d['tight_specs']>=87 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'TurboLean/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$TURBO_BIN" --json audit-spec lean/LeanNative/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']==d['total_specs_audited'] and d['tight_specs']>=110 and len(d.get('horizontal_packing_warnings',[]))==0, d; print(f'LeanNative/Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight (0 warnings)')"
  "$TURBO_BIN" --json ci-verify --project-dir lean --mode trusted --receipt /tmp/ci-receipt.json >/dev/null
  rm -f /tmp/ci-receipt.json
fi

echo "[2b/3] Checking HeapObj contract clause→regression table (docs/HEAPOBJ_CONTRACT.md)..."
python3 - <<'PY'
import re

# Roots: the evaluator, heap operations, LLVM emitter and translation validator under test. A contract predicate
# must reach one of these through the module's own defs (so it observes the system, not a constant).
ROOTS = {"evalCode", "evalExpr", "evalIncRef", "evalDecRef", "decRefObj", "incRefObj", "decRefBuf",
         "writeElemExclusive", "emitDeclLLVM", "emitRuntimeAndCAbiHelpers", "findUnsupportedLLVMCallInCode",
         "validateTranslationDecl", "getCtorLayout"}
XMARK = "-- XFAIL(heapobj-contract): flips in 5b"
TRIVIAL = re.compile(r"^#guard\s+(?:!\s*)?\(?\s*(?:true|false|decide\s+True|\(\)|1\s*==\s*1)\s*\)?\s*$")

def defs(src):
    """name -> body text (top-level `def`, up to the next column-0 line)."""
    out, lines = {}, src.split("\n")
    for i, l in enumerate(lines):
        m = re.match(r"^(?:private\s+)?(?:partial\s+)?def\s+([\w.']+)", l)
        if m:
            j = i + 1
            while j < len(lines) and (lines[j] == "" or lines[j][0] == " "):
                j += 1
            out[m.group(1)] = "\n".join(lines[i:j])
    return out

def reaches_root(ds):
    short = {}
    for n in ds:
        short.setdefault(n.split(".")[-1], set()).add(n)
    def deps(n):
        toks = set(re.findall(r"[A-Za-z_][\w']*", ds[n].split(":=", 1)[-1] if ":=" in ds[n] else ds[n]))
        return toks, {d for t in toks for d in short.get(t, ()) if d != n}
    good = set()
    changed = True
    while changed:
        changed = False
        for n in ds:
            if n in good:
                continue
            toks, ds_ = deps(n)
            if toks & ROOTS or ds_ & good:
                good.add(n); changed = True
    return good

def blocks(src):
    """[(name, is_xfail, block_text)] for every `-- REGRESSION(name)` marker."""
    ms = list(re.finditer(r"^-- REGRESSION\((\w+)\)\n", src, re.M))
    ends = [m.start() for m in ms[1:]] + [len(src)]
    out = []
    for m, e in zip(ms, ends):
        body = src[m.end():e]
        stop = re.search(r"^(?:/-!|def |-- UNCOVERED|-- REGRESSION|end )", body, re.M)
        body = body[:stop.start()] if stop else body
        out.append((m.group(1), body.startswith(XMARK), body))
    return out

def check_module(src):
    """Return (regressions {name: xfail_predicate or None}, errors)."""
    errs, regs = [], {}
    ds = defs(src)
    good = reaches_root(ds)
    for l in src.split("\n"):
        if TRIVIAL.match(l.strip()):
            errs.append(f"trivial guard `{l.strip()}`")
    if src.count(XMARK) != len([b for b in blocks(src) if b[1]]) + 1:  # +1: the convention text in the docstring
        errs.append("stray/unmarked XFAIL marker")
    for name, xf, body in blocks(src):
        if name in regs:
            errs.append(f"duplicate REGRESSION {name}")
        cmds = [l for l in body.split("\n") if l.startswith("#guard")]
        if not cmds:
            errs.append(f"{name}: no #guard / #guard_msgs")
            regs[name] = None
            continue
        if not xf:
            regs[name] = None
            continue
        # XFAIL: the first command is `#guard !<pred>` and `<pred>` is a module `def … : Bool` documented as a
        # `Contract` that reaches the evaluator/emitter/validator.
        m = re.match(r"^#guard !([A-Za-z_][\w']*)\s*$", cmds[0])
        if not m:
            errs.append(f"{name}: XFAIL must start with `#guard !<contractPredicate>`, got `{cmds[0]}`")
            regs[name] = None
            continue
        pred = m.group(1)
        regs[name] = pred
        d = ds.get(pred)
        if d is None:
            errs.append(f"{name}: XFAIL predicate `{pred}` is not a def in the module")
            continue
        if not re.match(rf"^def {re.escape(pred)}\s*:\s*Bool\s*:=", d):
            errs.append(f"{name}: XFAIL predicate `{pred}` must be `def {pred} : Bool := …`")
        rhs = d.split(":=", 1)[1].strip()
        if re.fullmatch(r"\(?\s*(?:true|false|!\s*true|!\s*false)\s*\)?", rhs):
            errs.append(f"{name}: XFAIL predicate `{pred}` is a constant")
        if pred not in good:
            errs.append(f"{name}: XFAIL predicate `{pred}` does not reference the evaluator/emitter/validator")
        if not re.search(rf"/-- Contract[^\n]*(?:\n[^\n]*)*?-/\ndef {re.escape(pred)}\b", src):
            errs.append(f"{name}: XFAIL predicate `{pred}` lacks a `/-- Contract … -/` docstring")
    return regs, errs

# --- self-test: the checker must reject trivially-true / non-evaluator XFAILs and accept a real one ---
HDR = XMARK + "\n"
ok_mod = (HDR + "/-- Contract: x. -/\ndef pOk : Bool := (evalCode 1 env st c).isOk\n"
          "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !pOk\n")
assert check_module(ok_mod)[1] == [], check_module(ok_mod)[1]
bad = {
  "guard-true": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard true\n",
  "guard-not-false": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !false\n",
  "const-pred": HDR + "/-- Contract: x. -/\ndef pK : Bool := false\n-- REGRESSION(r)\n" + XMARK + " — why\n#guard !pK\n",
  "no-evaluator": HDR + "/-- Contract: x. -/\ndef pN : Bool := [1, 2].length == 3\n-- REGRESSION(r)\n" + XMARK + " — why\n#guard !pN\n",
  "positive-guard": HDR + "/-- Contract: x. -/\ndef pOk : Bool := (evalCode 1 env st c).isOk\n-- REGRESSION(r)\n" + XMARK + " — why\n#guard pOk\n",
  "undefined-pred": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !nowhere\n",
  "no-contract-doc": HDR + "def pOk : Bool := (evalCode 1 env st c).isOk\n-- REGRESSION(r)\n" + XMARK + " — why\n#guard !pOk\n",
  "pass-without-guard": HDR + "-- REGRESSION(r)\n-- comment only\n",
}
for k, m in bad.items():
    assert check_module(m)[1], f"checker self-test: `{k}` was not rejected"

# --- the real module and the §8 table ---
src = open("lean/LeanNative/Tests/HeapObjContract.lean").read()
doc = open("docs/HEAPOBJ_CONTRACT.md").read()
regs, errs = check_module(src)
assert not errs, "HeapObj contract module: " + "; ".join(errs)
rows = re.findall(r"^\|[^|]*\| `(\w+)` \| (pass|XFAIL) \| (?:`#guard !(\w+)`|—) \|$", doc, re.M)
table = {n: (p if s == "XFAIL" else None) for n, s, p in rows}
assert all((s == "XFAIL") == bool(p) for _, s, p in rows), "XFAIL rows must name `#guard !pred`; pass rows `—`"
assert regs == table, f"contract table out of sync: module={regs} doc={table}"
unc = re.findall(r"^-- UNCOVERED\(([\w.-]+)\):", src, re.M)
unc_doc = re.findall(r"^\| `([\w.-]+)` \| [^|]+ \|$", doc.split("### UNCOVERED clauses", 1)[1], re.M)
assert len(unc) == len(set(unc)) and set(unc) == set(unc_doc), f"UNCOVERED list out of sync: module={unc} doc={unc_doc}"
nx = sum(p is not None for p in regs.values())
print(f"HeapObj contract: {len(regs)} regressions, {nx} explicit XFAIL (flip in 5b), {len(unc)} UNCOVERED; "
      f"checker self-test rejected {len(bad)} malformed XFAILs")
PY

echo "[3/3] Building Lean & Rust workspace..."
(cd lean && lake build)
./lean/.lake/build/bin/lean-native-core self-test
./lean/.lake/build/bin/lean-native-core emit-cabi-bindings lean/LeanNative/Spec.lean --emit-rust /tmp/ln_cabi_check.rs --emit-swift /tmp/ln_cabi_check.swift --emit-modulemap /tmp/ln_cabi_check.modulemap
grep -q "lean_native_ntt_butterfly_fused_2layer_slice" /tmp/ln_cabi_check.rs
grep -q "pub unsafe fn leannative_verify_rc_mode_safe" /tmp/ln_cabi_check.rs
grep -q "@_silgen_name(\"leannative_verify_rc_mode_safe\")" /tmp/ln_cabi_check.swift
grep -q "module TurboLeanCABI" /tmp/ln_cabi_check.modulemap
rm -f /tmp/ln_cabi_check.rs /tmp/ln_cabi_check.swift /tmp/ln_cabi_check.modulemap
./lean/.lake/build/bin/turbo-lean-native self-test
cargo check --locked --release -j 1
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (0 sorryAx)"
