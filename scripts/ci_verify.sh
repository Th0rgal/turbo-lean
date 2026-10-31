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

# Structural part only (text): markers, `#guard !<pred>` as the first XFAIL command, table sync. Whether `<pred>`
# is a real contract predicate is decided by the Lean meta check in step [3b] over its ELABORATED definition.
XMARK = "-- XFAIL(heapobj-contract): flips in 5b"
TRIVIAL = re.compile(r"^#guard\s+(?:!\s*)?\(?\s*(?:true|false|decide\s+True|\(\)|1\s*==\s*1)\s*\)?\s*$")

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
        # XFAIL: the first command is `#guard !<pred>`; `<pred>` itself is checked in Lean ([3b]).
        m = re.match(r"^#guard !([A-Za-z_][\w']*)\s*$", cmds[0])
        if not m:
            errs.append(f"{name}: XFAIL must start with `#guard !<contractPredicate>`, got `{cmds[0]}`")
            regs[name] = None
            continue
        regs[name] = m.group(1)
    return regs, errs

# --- self-test of the structural part (predicate bodies are self-tested by the Lean meta check in [3b]) ---
HDR = XMARK + "\n"
ok_mod = HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !pOk\n"
assert check_module(ok_mod)[1] == [], check_module(ok_mod)[1]
bad = {
  "guard-true": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard true\n",
  "guard-not-false": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !false\n",
  "positive-guard": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard pOk\n",
  "compound-guard": HDR + "-- REGRESSION(r)\n" + XMARK + " — why\n#guard !(pOk && false)\n",
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
      f"structural self-test rejected {len(bad)} malformed XFAILs")
open("/tmp/heapobj_xfail_preds", "w").write(" ".join(p for p in regs.values() if p))
PY
HEAPOBJ_XFAIL_PREDS="$(cat /tmp/heapobj_xfail_preds)"
rm -f /tmp/heapobj_xfail_preds
export HEAPOBJ_XFAIL_PREDS

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

echo "[3b/3] HeapObj XFAIL predicates: Lean meta check over the elaborated definitions..."
(cd lean && lake env lean --stdin) <<'LEAN'
import LeanNative.Tests.HeapObjContract
open Lean Meta

namespace HeapObjXfailCheck

/-- Evaluator / heap ops / LLVM emitter / translation validator entry points under test. -/
def roots : List Name :=
  [``LeanNative.Semantics.evalCode, ``LeanNative.Semantics.evalExpr,
   ``LeanNative.Semantics.HeapState.evalIncRef, ``LeanNative.Semantics.HeapState.evalDecRef,
   ``LeanNative.Semantics.HeapState.decRefObj, ``LeanNative.Semantics.HeapState.incRefObj,
   ``LeanNative.Semantics.HeapState.decRefBuf, ``LeanNative.Semantics.HeapState.writeElemExclusive,
   ``LeanNative.Backend.LLVM.emitDeclLLVM, ``LeanNative.Backend.LLVM.emitRuntimeAndCAbiHelpers,
   ``LeanNative.Backend.LLVM.findUnsupportedLLVMCallInCode, ``LeanNative.Proofs.validateTranslationDecl,
   ``Lean.Compiler.LCNF.getCtorLayout]

/-- Definitions the reachability walk unfolds: the test module's own and the self-test's. -/
def isLocal (n : Name) : Bool :=
  [`LeanNative.Tests.HeapObjContract, `HeapObjXfailCheck.SelfTest].any (·.isPrefixOf n)

/-- Elaborated value of `n` with binders opened, mvars instantiated, zeta- (unused `let`/`have` dropped,
    used ones substituted) and beta-reduced. Comments and dead `let`s do not survive elaboration/zeta. -/
def reducedBody (n : Name) : MetaM (Option Expr) := do
  let some ci := (← getEnv).find? n | return none
  let some v := ci.value? (allowOpaque := true) | return none
  lambdaTelescope (← instantiateMVars v) fun _ b => do
    Core.betaReduce (← zetaReduce b)

/-- Some root is among `cs`, or occurs (transitively) in the zeta-reduced body of a local definition among them. -/
def reachesRoot (cs : List Name) : MetaM Bool := do
  if cs.any roots.contains then return true
  let mut seen : NameSet := {}
  let mut todo := cs.filter isLocal
  while true do
    match todo with
    | [] => return false
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      let some b ← reducedBody c | continue
      let cs := b.getUsedConstants
      if cs.any roots.contains then return true
      todo := cs.toList.filter isLocal ++ todo
  return false

/-- Errors for the XFAIL predicate `n`: `def n : Bool`, `/-- Contract … -/`, its zeta-reduced body does not
    `whnfR` to a `Bool` literal, and it reaches an evaluator / emitter / validator root. -/
def checkPred (n : Name) : MetaM (List String) := do
  let env ← getEnv
  let some ci := env.find? n | return [s!"{n}: not a definition"]
  let mut errs := []
  unless ci.type == .const ``Bool [] do errs := errs ++ [s!"{n}: type is not `Bool`"]
  let doc := (← findDocString? env n).getD ""
  unless (doc.trimAsciiStart.toString).startsWith "Contract" do errs := errs ++ [s!"{n}: no `/-- Contract … -/` docstring"]
  match ← reducedBody n with
  | none => errs := errs ++ [s!"{n}: has no value"]
  | some b =>
    -- Head-normalise with every definition unfoldable except the roots, which stay opaque: a genuine predicate
    -- gets stuck on (a match over) a root application; one whose value does not depend on a root — a literal, a
    -- dead `let`/`have`/argument, a dead `match`/`if`/`cond` branch, an alias of a constant — reduces to a literal.
    let r ← withCanUnfoldPred (fun cfg ci => do
        if roots.contains ci.name then return false else canUnfoldDefault cfg ci) (whnf b)
    if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then
      errs := errs ++ [s!"{n}: reduces to a Bool literal"]
    -- Reachability is from the residual `r`, so a root that only occurs in a discarded branch does not count.
    else unless ← reachesRoot r.getUsedConstants.toList do
      errs := errs ++ [s!"{n}: does not reach the evaluator/emitter/validator"]
  return errs

end HeapObjXfailCheck

namespace HeapObjXfailCheck.SelfTest
open LeanNative.Tests.HeapObjContract LeanNative.Semantics
/-- Contract: ok. -/ def pOk : Bool := (evalCode 1 env0 .empty retZero) matches .ok _
/-- Contract: ok via module defs. -/ def pVia : Bool := nestedTupleOwnershipRejected
def helperOk : Bool := (evalCode 1 env0 .empty retZero) matches .ok _
/-- Contract: ok via a local helper. -/ def pViaLocal : Bool := helperOk && true
/-- Contract: comment mentions the evaluator. -/ def pComment : Bool := false -- evalCode
/-- Contract: dead let. -/ def pLet : Bool := let _ := allocMalformedField; false
/-- Contract: dead have. -/ def pHave : Bool := have _ := evalCode 1 env0 .empty retZero; true
/-- Contract: constant (the `#guard true` case). -/ def pTrue : Bool := true
/-- Contract: no evaluator. -/ def pNoEval : Bool := [1, 2].length == 3
/-- Contract: dead let in a helper. -/ def pHelperBody : Bool := let _ := evalCode 1 env0 .empty retZero; false
/-- Contract: via a constant helper. -/ def pViaConstHelper : Bool := pHelperBody
/-- Contract: beta-dead argument. -/ def pBeta : Bool := (fun (_ : Except UBError (Val × HeapState)) => false) allocMalformedField
/-- Contract: dead branch. -/ def pMatchDead : Bool := match true with | true => false | false => helperOk
/-- Contract: cond dead branch. -/ def pCond : Bool := cond true false helperOk
/-- Contract: alias of a constant helper with a live root elsewhere. -/ def pAliasConst : Bool := match pTrue with | true => false | false => helperOk
def pNoDoc : Bool := (evalCode 1 env0 .empty retZero) matches .ok _
/-- Contract: not Bool. -/ def pNat : Nat := if (evalCode 1 env0 .empty retZero) matches .ok _ then 1 else 0
end HeapObjXfailCheck.SelfTest

open HeapObjXfailCheck in
#eval show MetaM Unit from do
  let st := `HeapObjXfailCheck.SelfTest
  for p in [`pOk, `pVia, `pViaLocal] do
    let e ← checkPred (st ++ p)
    unless e.isEmpty do throwError "checker self-test: valid {p} rejected: {e}"
  let bad := [`pComment, `pLet, `pHave, `pTrue, `pNoEval, `pViaConstHelper, `pBeta, `pMatchDead, `pCond,
    `pAliasConst, `pNoDoc, `pNat]
  for p in bad do
    if (← checkPred (st ++ p)).isEmpty then throwError "checker self-test: malformed {p} accepted"
  let preds := ((← IO.getEnv "HEAPOBJ_XFAIL_PREDS").getD "").splitOn " " |>.filter (· != "")
  if preds.isEmpty then throwError "no XFAIL predicates given"
  let errs ← preds.flatMapM fun p => checkPred (`LeanNative.Tests.HeapObjContract ++ p.toName)
  unless errs.isEmpty do throwError "XFAIL predicates: {errs}"
  IO.println s!"XFAIL meta check: {preds.length} predicates reach the evaluator/emitter/validator; self-test rejected {bad.length} malformed"
LEAN

cargo check --locked --release -j 1
echo "[turbo-lean] ALL CI VERIFICATION GATES PASSED (0 sorryAx)"
