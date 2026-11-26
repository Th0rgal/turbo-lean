#!/usr/bin/env python3
"""H1.4 proof-mutant kill matrix over the proved LCNF lowering path.

Measures what the proof stack actually constrains: each mutant is a small
semantic edit to the lowering source (`lean/LeanNative/IR/RealLCNFBridge.lean`)
or its shared proved-path helpers (`lean/LeanNative/IR/RealLCNFShared.lean`),
applied in a throwaway git worktree seeded from the local `lean/.lake` build
cache. The kill signal is a failed `lake build LeanNative` of the proofs/Tests
closure (theorem elaboration failure or a failed `#guard` executable guard),
never a hand-judged verdict.

Honesty rules this harness enforces:
  * The committed originals are never touched: mutations happen only in a
    scratch worktree under `.h14-mutants/` inside the repository root, created
    with `git worktree add --detach` and removed with `git worktree remove`.
  * Site enumeration is deterministic and tied to pinned file sha256s; a pin
    mismatch fails closed (the matrix owner re-enumerates and re-pins).
  * A mutant whose own module fails to elaborate is NOT_APPLICABLE (stillborn),
    never counted as KILLED: it measures Lean's type checker, not the proofs.
  * Infrastructure failures (OOM, disk, download) are INFRA, never a kill.
  * `lean/.lake/build` is restored from a pristine snapshot before every mutant
    (the `scripts/emitter_mutants.py` shape), so one mutant's partial build
    cannot contaminate the next verdict.

CI runs `--self-test` (planted always-survives / always-killed / stillborn
controls through the real classifier) plus the bounded pinned sample
(`--sample ci`, members in CI_SAMPLE below, every one measured KILLED by the
full matrix). The full matrix (`--full`) takes hours and runs on demand.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "proof-mutant-matrix-v1"
SCRATCH_DIRNAME = ".h14-mutants"

FILES: Dict[str, str] = {
    "RB": "lean/LeanNative/IR/RealLCNFBridge.lean",
    "RS": "lean/LeanNative/IR/RealLCNFShared.lean",
}
MODULES: Dict[str, str] = {
    "RB": "LeanNative.IR.RealLCNFBridge",
    "RS": "LeanNative.IR.RealLCNFShared",
}
# Enumeration is only meaningful against these exact bytes (the same honesty
# rule as `scripts/lcnf_coverage_results.json`'s bridge_file_sha256 pins).
PINNED_SHA256: Dict[str, str] = {
    "RB": "cc32468508d6aa1bd2d907b0a2b5a3f1818082000729e38e551b37943d001848",
    "RS": "d00987d486ad389b209205ef63866cddb1c134235bf5eae2c96057c2cac4436e",
}
CLOSURE_TARGETS: List[str] = ["LeanNative"]

# Signatures that mean the build infrastructure failed, not the proof stack
# (subset of scripts/emitter_mutants.json `infra_signatures`).
INFRA_SIGNATURES: Tuple[str, ...] = (
    "out of memory",
    "oom-kill",
    "cannot allocate memory",
    "signal: 9",
    "sigkill",
    "no space left on device",
    "network is unreachable",
    "connection timed out",
    "connection refused",
    "failed to download",
    "elan toolchain install",
    "toolchain download",
)


@dataclass(frozen=True)
class Operator:
    name: str
    file_tag: str  # key into FILES
    pattern: str  # python regex, matched against the pinned bytes
    replacement: str  # re template (backrefs allowed)
    category: str  # one of the brief's operator classes
    expected_count: int  # pinned occurrence count at PINNED_SHA256
    description: str


# The explicit operator set. Categories map onto the H1.4 brief's list:
# operand swap, constant off-by-one, branch-condition flip, dropped statement,
# wrong constructor/tag, swapped arguments.
OPERATORS: List[Operator] = [
    # --- RealLCNFBridge.lean (RB) ---
    Operator("ite-swap", "RB", r"\.ite (\w+) (\w+) (\w+)", r".ite \1 \3 \2",
             "branch-flip", 4,
             "swap the then/else arms of an emitted or matched .ite"),
    Operator("incdec-swap", "RB",
             r"if isInc then \.incRef vid n kCode else \.decRef vid n kCode",
             "if isInc then .decRef vid n kCode else .incRef vid n kCode",
             "wrong-ctor-tag", 1,
             "emit decRef for incRef and vice versa in lowerRefOpPure"),
    Operator("opnd-swap", "RB", r"lMasked rMasked", "rMasked lMasked",
             "operand-swap", 5,
             "swap the masked operands of a lowered scalar binop"),
    Operator("neg-swap", "RB",
             r"ScalarExpr\.binOp \.sub \(\.constU64 0\) \(\.var arg\)",
             "ScalarExpr.binOp .sub (.var arg) (.constU64 0)",
             "operand-swap", 1,
             "turn UIntN.neg lowering (0 - x) into the identity (x - 0)"),
    Operator("minmax-swap", "RB", r"some \(min srcMask dstMask\)",
             "some (max srcMask dstMask)", "swapped-args", 1,
             "widening/narrowing cast picks the wider instead of narrower mask"),
    Operator("mask-drop", "RB",
             r"if mask == 0xFFFFFFFFFFFFFFFF then raw else \.binOp \.bitAnd raw \(\.constU64 mask\)",
             "raw", "dropped-stmt", 4,
             "drop the width mask on a lowered scalar result"),
    Operator("shiftmask-drop", "RB",
             r"if sMask == 63 then rMasked else \.binOp \.bitAnd rMasked \(\.constU64 sMask\)",
             "rMasked", "dropped-stmt", 2,
             "drop the shift-amount mask on shl/shr lowering"),
    Operator("restore-drop", "RB",
             r"\{ (stOut|st1) with fvarMap := savedFVars, activeCtor := savedActive, jpDecls := savedJps \}",
             r"\1", "dropped-stmt", 4,
             "drop the per-alternative bridge-state restore (binding scope leak)"),
    Operator("ctorhint-drop", "RB",
             r"match discr\?\.bind st\.lookupFVar\? with \| some dv => st\.setActiveCtor dv info\.name \| none => st",
             "st", "dropped-stmt", 2,
             "drop the discriminant constructor refinement inside a cases alternative"),
    Operator("fresh-offby1", "RB", r"nextVarId := vid \+ 1",
             "nextVarId := vid + 2", "const-offby1", 2,
             "SSA freshness allocator skips ids (freshVar/allocFreshFVar)"),
    Operator("altidx-offby1", "RB", r"idx \+ 1, discr\?",
             "idx + 2, discr?", "const-offby1", 2,
             "cases-alternative index advances by 2 (wrong fallback tag)"),
    Operator("rettyfuel-offby1", "RB", r"inferReturnedTypePure \(fuel \+ 16\)",
             "inferReturnedTypePure (fuel + 17)", "const-offby1", 1,
             "returned-type inference budget off by one"),
    Operator("cidx0-flip", "RB", r"if cidx == 0 then \.ite condVar no yes",
             "if cidx == 1 then .ite condVar no yes", "branch-flip", 1,
             "boolean tag-branch cidx 0 arm keyed on cidx 1"),
    Operator("tag-offby1", "RB", r"\.constU64 cidx\.toUInt64",
             ".constU64 (cidx.toUInt64 + 1)", "wrong-ctor-tag", 3,
             "emitted constructor tag constant off by one"),
    Operator("boolconst-f2t", "RB", r"\.constBool false", ".constBool true",
             "wrong-ctor-tag", 3,
             "emitted boolean false constant flipped to true"),
    Operator("boolconst-t2f", "RB", r"\.constBool true", ".constBool false",
             "wrong-ctor-tag", 4,
             "emitted boolean true constant flipped to false"),
    Operator("castguard-flip", "RB", r"if src != dst &&", "if src == dst &&",
             "branch-flip", 1,
             "uint-cast table walk admits only the self-cast pair"),
    Operator("retpin-flip", "RB", r"if dst == rv then some ty else none",
             "if dst != rv then some ty else none", "branch-flip", 1,
             "returned-type inference keys on the wrong binder"),
    Operator("fvarfilter-flip", "RB", r"\.filter \(fun \(f, _\) => f != fvarId\)",
             ".filter (fun (f, _) => f == fvarId)", "branch-flip", 2,
             "fvar-map rebind filter inverted (stale/shadowed bindings kept)"),
    Operator("vidfilter-flip", "RB", r"\.filter \(fun \(v, _\) => v != vid\)",
             ".filter (fun (v, _) => v == vid)", "branch-flip", 4,
             "var-type/active-ctor rebind filter inverted"),
    Operator("fvarlookup-flip", "RB", r"\.find\? \(fun \(f, _\) => f == fvarId\)",
             ".find? (fun (f, _) => f != fvarId)", "branch-flip", 1,
             "fvar-map lookup finds any OTHER binding"),
    Operator("objslots-flip", "RB", r"if args\.size != spec\.objSlots then",
             "if args.size == spec.objSlots then", "branch-flip", 1,
             "C1.2 ctor object-slot arity check inverted"),
    Operator("litbool-flip", "RB", r"\.constBool \(masked != 0\)",
             ".constBool (masked == 0)", "branch-flip", 1,
             "boolean literal lowering inverted"),
    # --- RealLCNFShared.lean (RS): proved-path helpers shared with the
    #     independent semantics (the differential's shared trusted component) ---
    Operator("namelookup-flip", "RS", r"\.find\? \(fun \(n, _\) => n == fnName\)",
             ".find? (fun (n, _) => n != fnName)", "branch-flip", 2,
             "ctx local-callee / gfSimd name lookup inverted"),
    Operator("canonlookup-flip", "RS",
             r"\.find\? \(fun \(n, _, _\) => n == fnName\)",
             ".find? (fun (n, _, _) => n != fnName)", "branch-flip", 1,
             "canonical scalar binop table lookup inverted"),
    Operator("jmpdetect-false", "RS",
             r"\| \.jmp fvarId _ => fvarId == targetFVar",
             "| .jmp fvarId _ => false", "branch-flip", 1,
             "recursive join-point detector never fires (fail-open)"),
    Operator("orderalts-id", "RS",
             r"alts\.filter \(fun \| \.default _ => false \| _ => true\) \+\+ alts\.filter \(fun \| \.default _ => true \| _ => false\)",
             "alts", "dropped-stmt", 1,
             "cases alternatives left unordered (default may precede ctors)"),
    Operator("widthmask-i8", "RS", r"\| \.i8 => some 0xFF\b",
             "| .i8 => some 0x7F", "const-offby1", 1,
             "8-bit width mask loses its top bit"),
    Operator("usizemask-swap", "RS",
             r"if arch\.isILP32 then 0xFFFFFFFF else 0xFFFFFFFFFFFFFFFF",
             "if arch.isILP32 then 0xFFFFFFFFFFFFFFFF else 0xFFFFFFFF",
             "swapped-args", 1,
             "USize mask branches swapped (64-bit arch masked to 32 bits)"),
    Operator("typeeqfuel-1", "RS", r"lnirTypeEqFuel 32 a b",
             "lnirTypeEqFuel 1 a b", "const-offby1", 1,
             "structural type equality truncated at depth 1"),
    Operator("tupleguard-oror", "RS",
             r"!fs\.isEmpty && fs\.all isFlatUnboxedScalar",
             "!fs.isEmpty || fs.all isFlatUnboxedScalar", "branch-flip", 1,
             "unboxed-tuple predicate admits non-scalar fields"),
]

# Pinned CI sample: a bounded, representative subset the nightly workflow runs.
# Every member was measured KILLED by the full matrix at the pinned shas; the
# CI job fails if any stops being killed (a proof/guard was weakened) or if a
# pin drifts (re-run --full and re-pin).
CI_SAMPLE: List[Tuple[str, str]] = [
    ("RB-opnd-swap-00", "KILLED"),
    ("RB-mask-drop-00", "KILLED"),
    ("RB-ite-swap-01", "KILLED"),
    ("RB-tag-offby1-00", "KILLED"),
    ("RB-restore-drop-01", "KILLED"),
    ("RS-widthmask-i8-00", "KILLED"),
]


@dataclass
class Mutant:
    mid: str
    file_tag: str
    op: str
    category: str
    occ: int  # occurrence index of the operator's pattern in the file
    line: int
    before: str
    after: str
    description: str


@dataclass
class BuildResult:
    rc: int
    output: str
    duration_s: float


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_sources(root: Path) -> Dict[str, str]:
    return {tag: (root / rel).read_text(encoding="utf-8") for tag, rel in FILES.items()}


def check_pins(srcs: Dict[str, str]) -> List[str]:
    errs = []
    for tag, text in srcs.items():
        actual = sha256_bytes(text.encode("utf-8"))
        if actual != PINNED_SHA256[tag]:
            errs.append(
                f"{FILES[tag]}: sha256 {actual} != pinned {PINNED_SHA256[tag]} "
                f"(source drifted; re-run --full, update PINNED_SHA256, "
                f"expected_count fields and CI_SAMPLE)")
    return errs


def enumerate_mutants(srcs: Dict[str, str]) -> Tuple[List[Mutant], List[str]]:
    """Deterministic site enumeration: operators in declaration order, matches
    in byte order. Returns (mutants, errors)."""
    mutants: List[Mutant] = []
    errs: List[str] = []
    for op in OPERATORS:
        text = srcs[op.file_tag]
        matches = list(re.finditer(op.pattern, text))
        if len(matches) != op.expected_count:
            errs.append(f"operator {op.name} ({op.file_tag}): found "
                        f"{len(matches)} sites, pinned {op.expected_count}")
        for i, m in enumerate(matches):
            after = m.expand(op.replacement)
            if after == m.group(0):
                errs.append(f"operator {op.name} occurrence {i}: replacement "
                            f"equals original (not a mutation)")
            line = text.count("\n", 0, m.start()) + 1
            mutants.append(Mutant(
                mid=f"{op.file_tag}-{op.name}-{i:02d}",
                file_tag=op.file_tag, op=op.name, category=op.category,
                occ=i, line=line, before=m.group(0), after=after,
                description=op.description))
    mids = [m.mid for m in mutants]
    if len(set(mids)) != len(mids):
        errs.append("duplicate mutant ids in enumeration")
    return mutants, errs


def apply_mutant(text: str, mutant: Mutant) -> str:
    op = next(o for o in OPERATORS if o.name == mutant.op and o.file_tag == mutant.file_tag)
    matches = list(re.finditer(op.pattern, text))
    if mutant.occ >= len(matches):
        raise RuntimeError(f"{mutant.mid}: occurrence {mutant.occ} not found "
                           f"({len(matches)} matches)")
    m = matches[mutant.occ]
    return text[:m.start()] + m.expand(op.replacement) + text[m.end():]


def lake_env() -> Dict[str, str]:
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    env.setdefault("LEAN_NUM_THREADS", "4")
    env["TURBO_LEAN_REMOTE_CACHE"] = ""
    env["TURBO_LEAN_REMOTE_TOKEN"] = ""
    return env


class LakeRunner:
    """Real build runner. --self-test swaps this for planted fakes."""

    def __init__(self, lean_dir: Path, timeout_s: int):
        self.lean_dir = lean_dir
        self.timeout_s = timeout_s

    def build(self, targets: List[str]) -> BuildResult:
        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                ["lake", "build"] + targets, cwd=str(self.lean_dir),
                env=lake_env(), capture_output=True, text=True,
                timeout=self.timeout_s)
            out = proc.stdout + "\n" + proc.stderr
            return BuildResult(proc.returncode, out, time.monotonic() - t0)
        except subprocess.TimeoutExpired as e:
            out = (e.stdout or "") if isinstance(e.stdout, str) else ""
            return BuildResult(124, out + "\n[proof-mutant-matrix] build timeout",
                               time.monotonic() - t0)


FAIL_MOD_RE = re.compile(r"[✖×] \[\d+/\d+\][^\n]*?(?:Building|Compiling|Running) ([A-Za-z0-9_.']+)")
ERROR_PATH_RE = re.compile(r"([A-Za-z0-9_./-]+\.lean):(\d+):(\d+):")


def is_infra(output: str) -> bool:
    low = output.lower()
    return any(sig in low for sig in INFRA_SIGNATURES)


def first_error_line(output: str) -> Optional[str]:
    for ln in output.splitlines():
        if "error:" in ln or "error: " in ln:
            return ln.strip()[:400]
    return None


def killed_by_module(output: str) -> Optional[str]:
    m = FAIL_MOD_RE.search(output)
    if m:
        return m.group(1)
    e = first_error_line(output)
    if e:
        pm = ERROR_PATH_RE.search(e)
        if pm:
            rel = pm.group(1)
            rel = rel[rel.find("LeanNative"):] if "LeanNative" in rel else rel
            return rel[:-5].replace("/", ".") if rel.endswith(".lean") else rel
    return None


def classify(module_res: BuildResult, closure_res: Optional[BuildResult]) -> Dict[str, object]:
    if is_infra(module_res.output) or (closure_res and is_infra(closure_res.output)):
        return {"outcome": "INFRA", "killed_by": None,
                "first_error": first_error_line((closure_res or module_res).output),
                "reason": "infrastructure signature in build output (unmeasured)"}
    if module_res.rc != 0:
        return {"outcome": "NOT_APPLICABLE", "killed_by": None,
                "first_error": first_error_line(module_res.output),
                "reason": "stillborn: mutated module itself fails to elaborate"}
    assert closure_res is not None
    if closure_res.rc != 0:
        return {"outcome": "KILLED", "killed_by": killed_by_module(closure_res.output),
                "first_error": first_error_line(closure_res.output), "reason": None}
    return {"outcome": "SURVIVED", "killed_by": None, "first_error": None,
            "reason": None}


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root)] + list(args),
                          capture_output=True, text=True, check=True).stdout.strip()


class Scratch:
    """One throwaway git worktree + .lake seed + pristine build snapshot."""

    def __init__(self, root: Path, base: Path, idx: int, commit: str, timeout_s: int):
        assert base.name == SCRATCH_DIRNAME and base.parent == root
        self.root = root
        self.base = base
        self.path = base / f"w{idx}"
        self.snap = base / f"snap{idx}"
        self.commit = commit
        self.runner = LakeRunner(self.path / "lean", timeout_s)

    def create(self) -> None:
        if self.path.exists():
            self.remove()
        self.base.mkdir(exist_ok=True)
        subprocess.run(["git", "-C", str(self.root), "worktree", "add",
                        "--detach", str(self.path), self.commit],
                       capture_output=True, text=True, check=True)
        shutil.copytree(self.root / "lean" / ".lake", self.path / "lean" / ".lake",
                        symlinks=True)

    def baseline(self) -> BuildResult:
        res = self.runner.build(CLOSURE_TARGETS)
        if res.rc == 0:
            if self.snap.exists():
                shutil.rmtree(self.snap)
            shutil.copytree(self.path / "lean" / ".lake" / "build", self.snap,
                            symlinks=True)
        return res

    def restore(self, pristine: Dict[str, str]) -> None:
        build = self.path / "lean" / ".lake" / "build"
        if build.exists():
            shutil.rmtree(build)
        shutil.copytree(self.snap, build, symlinks=True)
        for tag, text in pristine.items():
            (self.path / FILES[tag]).write_text(text, encoding="utf-8")

    def write_mutant(self, pristine: Dict[str, str], mutant: Mutant) -> None:
        mutated = apply_mutant(pristine[mutant.file_tag], mutant)
        (self.path / FILES[mutant.file_tag]).write_text(mutated, encoding="utf-8")

    def remove(self) -> None:
        # The brief's deletion rule: scratch worktrees are removed with
        # `git -C <worktree> worktree remove <literal path we created>`.
        subprocess.run(["git", "-C", str(self.root), "worktree", "remove",
                        "--force", str(self.path)], capture_output=True, text=True)
        if self.path.exists():
            shutil.rmtree(self.path)

    def drop_snapshot(self) -> None:
        if self.snap.exists():
            shutil.rmtree(self.snap)


def run_one(scratch: Scratch, pristine: Dict[str, str], mutant: Mutant,
            runner: Optional[object] = None) -> Dict[str, object]:
    r = runner or scratch.runner
    scratch.restore(pristine)
    scratch.write_mutant(pristine, mutant)
    t0 = time.monotonic()
    module_res = r.build([f"+{MODULES[mutant.file_tag]}"])
    closure_res = r.build(CLOSURE_TARGETS) if module_res.rc == 0 else None
    verdict = classify(module_res, closure_res)
    rec = {
        "id": mutant.mid, "file": FILES[mutant.file_tag], "line": mutant.line,
        "operator": mutant.op, "category": mutant.category,
        "before": mutant.before, "after": mutant.after,
        "duration_s": round(time.monotonic() - t0, 1),
    }
    rec.update(verdict)
    scratch.restore(pristine)
    return rec


def run_matrix(mutants: List[Mutant], pristine: Dict[str, str], workers: int,
               timeout_s: int, keep_scratch: bool) -> List[Dict[str, object]]:
    commit = git(ROOT, "rev-parse", "HEAD")
    base = ROOT / SCRATCH_DIRNAME
    scratches = [Scratch(ROOT, base, i, commit, timeout_s) for i in range(workers)]
    chunks: List[List[Mutant]] = [[] for _ in range(workers)]
    for i, m in enumerate(mutants):
        chunks[i % workers].append(m)
    results: List[Dict[str, object]] = []
    try:
        for s in scratches:
            print(f"[setup] creating scratch worktree {s.path} at {commit[:12]}",
                  flush=True)
            s.create()
            base_res = s.baseline()
            if base_res.rc != 0:
                raise RuntimeError(
                    f"baseline closure build failed in {s.path} "
                    f"(rc={base_res.rc}): {first_error_line(base_res.output)}")
            jm = re.search(r"Build completed successfully \((\d+) jobs\)",
                           base_res.output)
            print(f"[setup] {s.path.name}: baseline green "
                  f"({jm.group(1) if jm else '?'} jobs, "
                  f"{base_res.duration_s:.0f}s)", flush=True)

        def worker(idx: int) -> List[Dict[str, object]]:
            out = []
            for m in chunks[idx]:
                rec = run_one(scratches[idx], pristine, m)
                print(f"[{rec['outcome']:>14}] {rec['id']:28s} line {rec['line']:<4} "
                      f"{rec.get('killed_by') or ''} ({rec['duration_s']}s)",
                      flush=True)
                out.append(rec)
            return out

        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            for part in ex.map(worker, range(workers)):
                results.extend(part)
    finally:
        if not keep_scratch:
            for s in scratches:
                s.remove()
                s.drop_snapshot()
            if base.exists() and not any(base.iterdir()):
                base.rmdir()
    results.sort(key=lambda r: r["id"])
    return results


def summarize(results: List[Dict[str, object]]) -> Dict[str, object]:
    total = len(results)
    counts = {k: sum(1 for r in results if r["outcome"] == k)
              for k in ("KILLED", "SURVIVED", "NOT_APPLICABLE", "INFRA")}
    denom = total - counts["NOT_APPLICABLE"] - counts["INFRA"]
    by_cat: Dict[str, Dict[str, int]] = {}
    for r in results:
        c = by_cat.setdefault(str(r["category"]), {"KILLED": 0, "SURVIVED": 0,
                                                   "NOT_APPLICABLE": 0, "INFRA": 0})
        c[str(r["outcome"])] += 1
    return {
        "total_mutants": total,
        "killed": counts["KILLED"],
        "survived": counts["SURVIVED"],
        "not_applicable_stillborn": counts["NOT_APPLICABLE"],
        "infra_unmeasured": counts["INFRA"],
        "denominator_valid_mutants": denom,
        "coverage": f"{counts['KILLED']}/{denom}",
        "coverage_pct": round(100.0 * counts["KILLED"] / denom, 1) if denom else None,
        "by_category": by_cat,
    }


# ---------------------------------------------------------------------------
# Self-test: planted controls through the REAL classifier, no Lean build.
# ---------------------------------------------------------------------------

class PlantedRunner:
    """Planted build outcomes keyed by call order: first call is the module
    stage, second the closure stage."""

    def __init__(self, outcomes: List[BuildResult]):
        self.outcomes = list(outcomes)
        self.calls = 0

    def build(self, targets: List[str]) -> BuildResult:
        res = self.outcomes[min(self.calls, len(self.outcomes) - 1)]
        self.calls += 1
        return res


def self_test() -> int:
    failures: List[str] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        line = f"[self-test] {'PASS' if cond else 'FAIL'}: {name}"
        if detail and not cond:
            line += f" — {detail}"
        print(line)
        if not cond:
            failures.append(name)

    srcs = read_sources(ROOT)
    pin_errs = check_pins(srcs)
    check("pinned source sha256s match the tree", not pin_errs, "; ".join(pin_errs))

    mutants, errs = enumerate_mutants(srcs)
    check("deterministic enumeration has pinned per-operator counts", not errs,
          "; ".join(errs))
    mutants2, _ = enumerate_mutants(srcs)
    check("enumeration is deterministic (two runs identical)",
          [m.mid for m in mutants] == [m.mid for m in mutants2])
    check("every CI sample id exists in the enumeration",
          all(any(m.mid == mid for m in mutants) for mid, _ in CI_SAMPLE),
          str([mid for mid, _ in CI_SAMPLE
               if not any(m.mid == mid for m in mutants)]))

    # Every mutant applies as exactly one contiguous differing region whose
    # old/new text sits inside the recorded before/after. (A replacement may
    # itself still match the operator's pattern — ite-swap does — so pattern
    # match counts cannot measure single-site application.)
    bad_apply: List[str] = []
    for m in mutants:
        orig = srcs[m.file_tag]
        mutated = apply_mutant(orig, m)
        if mutated == orig:
            bad_apply.append(f"{m.mid}: no byte change")
            continue
        if len(mutated) - len(orig) != len(m.after) - len(m.before):
            bad_apply.append(f"{m.mid}: length delta mismatch")
            continue
        pre = 0
        lim = min(len(orig), len(mutated))
        while pre < lim and orig[pre] == mutated[pre]:
            pre += 1
        suf = 0
        while (suf < lim - pre
               and orig[len(orig) - 1 - suf] == mutated[len(mutated) - 1 - suf]):
            suf += 1
        changed_orig = orig[pre:len(orig) - suf]
        changed_new = mutated[pre:len(mutated) - suf]
        if m.before.find(changed_orig) == -1 or m.after.find(changed_new) == -1:
            bad_apply.append(f"{m.mid}: diff region escapes the recorded site "
                             f"({changed_orig!r} -> {changed_new!r})")
    check("applying a mutant changes the bytes", bool(mutants) and not any(
        "no byte change" in b for b in bad_apply))
    check("every mutant application is single-site at its recorded text",
          not bad_apply, "; ".join(bad_apply[:4]))

    ok = BuildResult(0, "Build completed successfully (3 jobs)", 1.0)
    kill_out = ("✖ [12/44] Building LeanNative.Proofs.RealLCNFBridgeProofs\n"
                "error: lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean:123:4: "
                "error: unsolved goals")
    killed = BuildResult(1, kill_out, 2.0)
    stillborn = BuildResult(1, "error: lean/LeanNative/IR/RealLCNFBridge.lean:10:1: "
                               "error: type mismatch", 1.0)
    infra = BuildResult(1, "ld: No space left on device", 1.0)

    # Planted always-survives control: both stages green must classify SURVIVED.
    v = classify(ok, ok)
    check("planted always-survives control classifies SURVIVED",
          v["outcome"] == "SURVIVED", str(v))
    # Planted always-killed control: closure stage red must classify KILLED
    # with the failing module parsed out.
    v = classify(ok, killed)
    check("planted always-killed control classifies KILLED",
          v["outcome"] == "KILLED", str(v))
    check("planted always-killed control names the killing module",
          v["killed_by"] == "LeanNative.Proofs.RealLCNFBridgeProofs", str(v))
    check("planted always-killed control captures the first error line",
          bool(v["first_error"]) and "unsolved goals" in str(v["first_error"]), str(v))
    v = classify(stillborn, None)
    check("planted stillborn control classifies NOT_APPLICABLE",
          v["outcome"] == "NOT_APPLICABLE", str(v))
    v = classify(ok, infra)
    check("planted infra control classifies INFRA (never a kill)",
          v["outcome"] == "INFRA", str(v))

    # The planted runner drives the same two-stage protocol run_one uses.
    pr = PlantedRunner([ok, killed])
    mres = pr.build(["+X"])
    cres = pr.build(CLOSURE_TARGETS) if mres.rc == 0 else None
    check("two-stage protocol with planted runner reaches the closure stage",
          pr.calls == 2 and classify(mres, cres)["outcome"] == "KILLED")

    print(f"[self-test] {'OK' if not failures else 'FAILED'} "
          f"({len(failures)} failure(s))")
    return 0 if not failures else 1


def write_results(path: Path, results: List[Dict[str, object]],
                  srcs: Dict[str, str]) -> None:
    toolchain = (ROOT / "lean" / "lean-toolchain").read_text().strip()
    doc = {
        "schemaVersion": SCHEMA,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "measured_commit": git(ROOT, "rev-parse", "HEAD"),
        "toolchain": toolchain,
        "kill_signal": "lake build " + " ".join(CLOSURE_TARGETS) +
                       " (proofs + Tests #guard closure)",
        "files": {FILES[t]: sha256_bytes(srcs[t].encode("utf-8")) for t in FILES},
        "operators": [{"name": o.name, "file": FILES[o.file_tag],
                       "category": o.category, "sites": o.expected_count,
                       "description": o.description} for o in OPERATORS],
        "summary": summarize(results),
        "mutants": results,
    }
    path.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    print(f"[results] wrote {path}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--self-test", action="store_true",
                    help="run planted-control self test (no Lean build)")
    ap.add_argument("--list", action="store_true",
                    help="print the enumerated mutant sites and exit")
    ap.add_argument("--full", action="store_true", help="run the full matrix")
    ap.add_argument("--sample", choices=["ci"],
                    help="run the pinned CI sample and assert expected outcomes")
    ap.add_argument("--mutants", default="",
                    help="comma-separated mutant ids to run")
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=3600,
                    help="per-build timeout in seconds")
    ap.add_argument("--json-out", default="",
                    help="write the results JSON to this path")
    ap.add_argument("--keep-scratch", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    srcs = read_sources(ROOT)
    pin_errs = check_pins(srcs)
    mutants, errs = enumerate_mutants(srcs)
    if pin_errs or errs:
        for e in pin_errs + errs:
            print(f"[proof-mutant-matrix] FAIL-CLOSED: {e}", file=sys.stderr)
        return 1

    if args.list:
        for m in mutants:
            print(f"{m.mid:30s} {FILES[m.file_tag]}:{m.line:<5} [{m.category}] "
                  f"{m.before!r} -> {m.after!r}")
        print(f"total: {len(mutants)} mutants over {len(FILES)} files")
        return 0

    selected: List[Mutant]
    expected: Dict[str, str] = {}
    if args.sample == "ci":
        wanted = {mid: exp for mid, exp in CI_SAMPLE}
        selected = [m for m in mutants if m.mid in wanted]
        expected = wanted
        if len(selected) != len(CI_SAMPLE):
            print("[proof-mutant-matrix] CI sample ids missing from enumeration",
                  file=sys.stderr)
            return 1
    elif args.mutants:
        ids = {s.strip() for s in args.mutants.split(",") if s.strip()}
        selected = [m for m in mutants if m.mid in ids]
        missing = ids - {m.mid for m in selected}
        if missing:
            print(f"[proof-mutant-matrix] unknown mutant ids: {sorted(missing)}",
                  file=sys.stderr)
            return 64
    elif args.full:
        selected = mutants
    else:
        ap.print_help()
        return 64

    print(f"[proof-mutant-matrix] running {len(selected)} mutant(s), "
          f"{args.workers} worker(s)")
    results = run_matrix(selected, srcs, max(1, args.workers), args.timeout,
                         args.keep_scratch)
    summary = summarize(results)
    print(json.dumps(summary, indent=2))

    if args.json_out:
        write_results(Path(args.json_out), results, srcs)

    rc = 0
    if summary["infra_unmeasured"]:
        print("[proof-mutant-matrix] INFRA outcomes present: unmeasured, rerun",
              file=sys.stderr)
        rc = 1
    if expected:
        for r in results:
            exp = expected.get(str(r["id"]))
            if exp and r["outcome"] != exp:
                print(f"[proof-mutant-matrix] CI sample regression: {r['id']} "
                      f"expected {exp}, got {r['outcome']}", file=sys.stderr)
                rc = 1
        if rc == 0:
            print(f"[proof-mutant-matrix] CI sample: {len(results)}/"
                  f"{len(CI_SAMPLE)} pinned mutants behaved as measured")
    return rc


if __name__ == "__main__":
    sys.exit(main())
