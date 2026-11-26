#!/usr/bin/env python3
"""H1.4 proof-mutant kill matrix over the proved LCNF lowering path.

Measures what the proof stack actually constrains: each mutant is a small
semantic edit to the lowering source (`lean/LeanNative/IR/RealLCNFBridge.lean`)
or its shared proved-path helpers (`lean/LeanNative/IR/RealLCNFShared.lean`),
applied in a throwaway git worktree seeded from the local `lean/.lake` build
cache. The kill signal is a failed `lake build LeanNative` of the proofs/Tests
closure (theorem elaboration failure or a failed `#guard` executable guard),
never a hand-judged verdict.

Honesty rules this harness enforces (round 1 of the harness review folded in):
  * The committed originals are never touched: mutations happen only in a
    scratch worktree under `.h14-mutants/` inside the repository root, created
    with `git worktree add --detach` and removed with `git worktree remove`
    (with `git worktree prune` around both, so a killed run cannot strand a
    registration).
  * The measured object is one COMMIT: pristine sources and pins are read with
    `git show <commit>:<path>` at the commit the scratch worktrees are built
    at, the run fails closed when the working tree's copies differ from that
    commit, and the results JSON records that same commit and its toolchain.
  * Site enumeration is deterministic and tied to pinned file sha256s; a pin
    mismatch fails closed (the matrix owner re-enumerates and re-pins).
  * A mutant whose own module fails to elaborate is NOT_APPLICABLE (stillborn),
    never counted as KILLED: it measures Lean's type checker, not the proofs.
  * A build timeout is TIMEOUT and an infrastructure failure (OOM 137, disk,
    download) is INFRA — both are unmeasured, never kills, and both make the
    run exit non-zero. Infra signatures are only consulted on failed builds, so
    a green build whose test output echoes one is still a SURVIVED. Builds run
    in their own process group and the whole group is SIGKILLed on timeout, so
    orphaned `lean` children cannot write into `.lake/build` across the
    pristine-snapshot restore boundary (cross-mutant contamination).
  * `lean/.lake/build` is restored from a pristine snapshot before every mutant
    (the `scripts/emitter_mutants.py` shape).
  * Every finished mutant is appended to a progress JSONL as it completes; a
    crashed or interrupted run resumes from it (`--resume`), and a per-mutant
    exception becomes an ERROR row instead of aborting the run.

CI runs `--self-test` (planted always-survives / always-killed / stillborn /
timeout / infra controls driven through the real `run_one` with a fake scratch)
plus the bounded pinned sample (`--sample ci`, members in CI_SAMPLE below,
every one recorded KILLED in the committed results JSON, which the self-test
checks). The full matrix (`--full`) takes hours and runs on demand.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "proof-mutant-matrix-v2"
SCRATCH_DIRNAME = ".h14-mutants"
RESULTS_PATH = ROOT / "scripts" / "proof_mutant_matrix_results.json"

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

# Outcomes that are a measurement (stay in the denominator and need no re-run).
TERMINAL_OUTCOMES = ("KILLED", "SURVIVED")
# Outcomes excluded from the denominator.
UNMEASURED_OUTCOMES = ("NOT_APPLICABLE", "INFRA", "TIMEOUT", "ERROR")

# Signatures that mean the build infrastructure failed, not the proof stack
# (subset of scripts/emitter_mutants.json `infra_signatures`, plus the form
# Lake prints when a child `lean` is OOM-killed). Only consulted on rc != 0,
# and only on error lines / the failing tail block (review r2 F3): a dependent
# module's own `info:`/`#eval` output inside an otherwise-real kill log must
# not turn the kill into INFRA. The loose substrings "sigkill" and bare
# "code 137" are gone for the same reason; rc 137 / -9 is the primary OOM
# evidence.
INFRA_SIGNATURES: Tuple[str, ...] = (
    "out of memory",
    "oom-kill",
    "cannot allocate memory",
    "signal: 9",
    "exited with code 137",
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
# Every member is recorded KILLED in the committed results JSON
# (scripts/proof_mutant_matrix_results.json), which --self-test checks; the CI
# job fails if any stops being killed (a proof/guard was weakened) or if a pin
# drifts (re-run --full and re-pin).
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


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root)] + list(args),
                          capture_output=True, text=True, check=True).stdout.strip()


def git_show(root: Path, commit: str, rel: str) -> str:
    """Byte-exact file content at a commit (no strip: the sha pins need the
    trailing newline)."""
    proc = subprocess.run(["git", "-C", str(root), "show", f"{commit}:{rel}"],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"git show {commit}:{rel} failed: {proc.stderr.strip()}")
    return proc.stdout


def read_sources_at(root: Path, commit: str) -> Dict[str, str]:
    """Pristine sources at the MEASURED commit — what scratch worktrees hold
    and what mutants apply to (review F1: never the working tree)."""
    return {tag: git_show(root, commit, rel) for tag, rel in FILES.items()}


def assert_sources_clean(root: Path, commit: str) -> List[str]:
    """Fail closed when the working tree's copies of the enumerated files
    differ from the measured commit (review F1)."""
    errs = []
    for tag, rel in FILES.items():
        proc = subprocess.run(
            ["git", "-C", str(root), "diff", "--quiet", commit, "--", rel],
            capture_output=True, text=True)
        if proc.returncode != 0:
            errs.append(f"{rel}: working tree differs from {commit[:12]} "
                        f"(commit or revert it; the matrix measures one commit)")
    return errs


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


def lake_env(tmpdir: Optional[Path] = None) -> Dict[str, str]:
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    env.setdefault("LEAN_NUM_THREADS", "4")
    env["TURBO_LEAN_REMOTE_CACHE"] = ""
    env["TURBO_LEAN_REMOTE_TOKEN"] = ""
    if tmpdir is not None:
        # Per-scratch TMPDIR and TURBO_LEAN_HOME: elaboration-time IO tests
        # write fixed-name files under $TMPDIR (Tests/EvalLCNFCLITests.lean's
        # json-noise fixture) and pack/cache state under TURBO_LEAN_HOME
        # (Tests/StochasticEvolveTests.lean; the nightly workflow isolates the
        # same variable per workspace), so concurrent workers sharing either
        # can fail each other's builds and record a false KILL for an
        # unrelated mutant.
        tmpdir.mkdir(parents=True, exist_ok=True)
        env["TMPDIR"] = str(tmpdir)
        cache = tmpdir / "turbo-cache"
        cache.mkdir(parents=True, exist_ok=True)
        env["TURBO_LEAN_HOME"] = str(cache)
    return env


class LakeRunner:
    """Real build runner. The self-test swaps this for planted fakes.

    Review F3: the build runs in its own process group and the WHOLE group is
    SIGKILLed on timeout, so orphaned `lean` children cannot keep writing into
    `.lake/build` across the next mutant's snapshot restore."""

    def __init__(self, lean_dir: Path, timeout_s: int):
        self.lean_dir = lean_dir
        self.timeout_s = timeout_s
        # Inside the scratch worktree, so `git worktree remove --force` and the
        # scratch cleanup take it with them.
        self.tmpdir = lean_dir.parent / ".h14-tmp"

    def build(self, targets: List[str]) -> BuildResult:
        t0 = time.monotonic()
        proc = subprocess.Popen(
            ["lake", "build"] + targets, cwd=str(self.lean_dir),
            env=lake_env(self.tmpdir), stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            out, _ = proc.communicate(timeout=self.timeout_s)
            return BuildResult(proc.returncode, out or "", time.monotonic() - t0)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                proc.kill()
            out, _ = proc.communicate()
            return BuildResult(
                124, (out or "") + "\n[proof-mutant-matrix] build timeout "
                "(process group SIGKILLed)", time.monotonic() - t0)


FAIL_MOD_RE = re.compile(r"[✖×] \[\d+/\d+\][^\n]*?(?:Building|Compiling|Running) ([A-Za-z0-9_.']+)")
ERROR_PATH_RE = re.compile(r"([A-Za-z0-9_./-]+\.lean):(\d+):(\d+):")


def infra_scan_lines(output: str) -> List[str]:
    """The lines infra signatures are matched against on a FAILED build: error
    lines plus the closing block that names the failing job (review r2 F3 —
    a rebuilt dependent module's own `info:`/`#eval` output elsewhere in the
    log must not turn a real kill into INFRA)."""
    lines = output.splitlines()
    return [ln for ln in lines if "error" in ln.lower()] + lines[-5:]


def is_infra(res: Optional[BuildResult]) -> bool:
    """Infra is only read off FAILED builds (review F4): a green build whose
    test output echoes a signature is not infra. An exit of 137 / -9
    (OOM-killed) is the primary OOM evidence; text signatures are matched on
    error lines and the failing tail block only (review r2 F3)."""
    if res is None or res.rc == 0:
        return False
    if res.rc in (137, -9):
        return True
    scan = "\n".join(infra_scan_lines(res.output)).lower()
    return any(sig in scan for sig in INFRA_SIGNATURES)


def is_timeout(res: Optional[BuildResult]) -> bool:
    return res is not None and res.rc == 124


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
    # Order matters (review F3/F4): timeout and infra are UNMEASURED and take
    # precedence over any kill/stillborn reading of the same rc.
    if is_timeout(module_res) or is_timeout(closure_res):
        return {"outcome": "TIMEOUT", "killed_by": None,
                "first_error": None,
                "reason": "build timeout (unmeasured, never a kill)"}
    if is_infra(module_res) or is_infra(closure_res):
        return {"outcome": "INFRA", "killed_by": None,
                "first_error": first_error_line((closure_res or module_res).output),
                "reason": "infrastructure signature or OOM exit on a failed "
                          "build (unmeasured, never a kill)"}
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
        # Review F5: a killed previous run can leave a registration whose
        # directory is gone; prune before add, and surface git's own stderr.
        subprocess.run(["git", "-C", str(self.root), "worktree", "prune"],
                       capture_output=True, text=True)
        self.base.mkdir(exist_ok=True)
        proc = subprocess.run(["git", "-C", str(self.root), "worktree", "add",
                               "--detach", str(self.path), self.commit],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(f"git worktree add {self.path} failed "
                               f"(rc={proc.returncode}): {proc.stderr.strip()}")
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
        proc = subprocess.run(["git", "-C", str(self.root), "worktree", "remove",
                               "--force", str(self.path)],
                              capture_output=True, text=True)
        if proc.returncode != 0 and self.path.exists():
            print(f"[scratch] git worktree remove {self.path} failed "
                  f"(rc={proc.returncode}): {proc.stderr.strip()}; "
                  f"falling back to rmtree + prune", file=sys.stderr)
            shutil.rmtree(self.path)
        # Review F5: drop the registration the rmtree fallback leaves behind.
        subprocess.run(["git", "-C", str(self.root), "worktree", "prune"],
                       capture_output=True, text=True)

    def drop_snapshot(self) -> None:
        if self.snap.exists():
            shutil.rmtree(self.snap)


def run_one(scratch, pristine: Dict[str, str], mutant: Mutant,
            runner: Optional[object] = None) -> Dict[str, object]:
    """Two-stage protocol: build the mutated module (stillborn check), then the
    proofs/Tests closure (kill check). The self-test drives THIS function with
    a fake scratch and planted runners (review F8)."""
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
    return rec


def safe_run_one(scratch, pristine: Dict[str, str], mutant: Mutant,
                 runner: Optional[object] = None) -> Dict[str, object]:
    """Review F6: a per-mutant exception becomes an ERROR row, never an abort."""
    try:
        return run_one(scratch, pristine, mutant, runner)
    except Exception as e:  # noqa: BLE001 - every failure becomes a row
        return {
            "id": mutant.mid, "file": FILES[mutant.file_tag], "line": mutant.line,
            "operator": mutant.op, "category": mutant.category,
            "before": mutant.before, "after": mutant.after,
            "duration_s": 0.0, "outcome": "ERROR", "killed_by": None,
            "first_error": None,
            "reason": f"harness exception: {type(e).__name__}: {e}",
        }


def load_progress(jsonl_path: Path, commit: str) -> Dict[str, Dict[str, object]]:
    """Resume rows from a prior interrupted run at the SAME commit. Only
    measured outcomes (KILLED/SURVIVED) and stillborns are reused; TIMEOUT,
    INFRA and ERROR re-run."""
    done: Dict[str, Dict[str, object]] = {}
    if not jsonl_path.exists():
        return done
    for ln in jsonl_path.read_text(encoding="utf-8").splitlines():
        ln = ln.strip()
        if not ln:
            continue
        rec = json.loads(ln)
        if rec.get("measured_commit") != commit:
            raise RuntimeError(
                f"{jsonl_path}: progress rows are for commit "
                f"{str(rec.get('measured_commit'))[:12]}, this run measures "
                f"{commit[:12]}; move the file aside")
        if rec.get("outcome") in TERMINAL_OUTCOMES + ("NOT_APPLICABLE",):
            done[str(rec["id"])] = rec
    return done


def run_matrix(mutants: List[Mutant], pristine: Dict[str, str], commit: str,
               workers: int, timeout_s: int, keep_scratch: bool,
               jsonl_path: Path, resume: bool) -> List[Dict[str, object]]:
    base = ROOT / SCRATCH_DIRNAME
    done = load_progress(jsonl_path, commit) if resume else {}
    todo = [m for m in mutants if m.mid not in done]
    if done:
        print(f"[resume] {len(done)} mutant(s) carried from {jsonl_path}, "
              f"{len(todo)} to run")
    if not resume and jsonl_path.exists():
        jsonl_path.unlink()
    workers = max(1, min(workers, max(1, len(todo))))  # review F7
    scratches = [Scratch(ROOT, base, i, commit, timeout_s) for i in range(workers)]
    chunks: List[List[Mutant]] = [[] for _ in range(workers)]
    for i, m in enumerate(todo):
        chunks[i % workers].append(m)
    results: List[Dict[str, object]] = list(done.values())
    jsonl_lock = threading.Lock()
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
                rec = safe_run_one(scratches[idx], pristine, m)
                rec["measured_commit"] = commit
                with jsonl_lock:
                    with jsonl_path.open("a", encoding="utf-8") as f:
                        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
                print(f"[{rec['outcome']:>14}] {rec['id']:28s} line {rec['line']:<4} "
                      f"{rec.get('killed_by') or ''} ({rec['duration_s']}s)",
                      flush=True)
                out.append(rec)
            # Review F7: one final restore per scratch (run_one no longer
            # restores after each mutant; the next mutant restores first).
            scratches[idx].restore(pristine)
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
              for k in TERMINAL_OUTCOMES + UNMEASURED_OUTCOMES}
    denom = counts["KILLED"] + counts["SURVIVED"]
    by_cat: Dict[str, Dict[str, int]] = {}
    for r in results:
        c = by_cat.setdefault(str(r["category"]), {})
        c[str(r["outcome"])] = c.get(str(r["outcome"]), 0) + 1
    return {
        "total_mutants": total,
        "killed": counts["KILLED"],
        "survived": counts["SURVIVED"],
        "not_applicable_stillborn": counts["NOT_APPLICABLE"],
        "infra_unmeasured": counts["INFRA"],
        "timeout_unmeasured": counts["TIMEOUT"],
        "error_unmeasured": counts["ERROR"],
        "denominator_valid_mutants": denom,
        "coverage": f"{counts['KILLED']}/{denom}",
        "coverage_pct": round(100.0 * counts["KILLED"] / denom, 1) if denom else None,
        "by_category": by_cat,
    }


# ---------------------------------------------------------------------------
# Self-test: planted controls driven through the REAL run_one (review F8),
# no Lean build.
# ---------------------------------------------------------------------------

class PlantedRunner:
    """Planted build outcomes keyed by call order: first call is the module
    stage, second the closure stage."""

    def __init__(self, outcomes: List[BuildResult]):
        self.outcomes = list(outcomes)
        self.calls = 0
        self.targets: List[List[str]] = []

    def build(self, targets: List[str]) -> BuildResult:
        res = self.outcomes[min(self.calls, len(self.outcomes) - 1)]
        self.calls += 1
        self.targets.append(list(targets))
        return res


class FakeScratch:
    """No-op scratch so the self-test can drive run_one without a worktree."""

    def __init__(self):
        self.restores = 0
        self.mutants_written: List[str] = []
        self.runner = None

    def restore(self, pristine: Dict[str, str]) -> None:
        self.restores += 1

    def write_mutant(self, pristine: Dict[str, str], mutant: Mutant) -> None:
        self.mutants_written.append(mutant.mid)


class RaisingScratch(FakeScratch):
    def write_mutant(self, pristine: Dict[str, str], mutant: Mutant) -> None:
        raise OSError("planted scratch failure")


def self_test() -> int:
    failures: List[str] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        line = f"[self-test] {'PASS' if cond else 'FAIL'}: {name}"
        if detail and not cond:
            line += f" — {detail}"
        print(line)
        if not cond:
            failures.append(name)

    commit = git(ROOT, "rev-parse", "HEAD")
    clean_errs = assert_sources_clean(ROOT, commit)
    check("enumerated sources in the working tree match HEAD (fail-closed)",
          not clean_errs, "; ".join(clean_errs))
    srcs = read_sources_at(ROOT, commit)
    pin_errs = check_pins(srcs)
    check("pinned source sha256s match the measured commit", not pin_errs,
          "; ".join(pin_errs))

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
    infra_fail = BuildResult(1, "ld: No space left on device", 1.0)
    oom_rc = BuildResult(137, "make: *** [all] Killed", 1.0)
    oom_text = BuildResult(1, "error: Lean exited with code 137", 1.0)
    timeout = BuildResult(124, "[proof-mutant-matrix] build timeout "
                               "(process group SIGKILLed)", 3600.0)
    green_with_sig = BuildResult(0, "info: simulated heap test: out of memory "
                                    "path exercised\nBuild completed "
                                    "successfully (44 jobs)", 2.0)
    m0 = mutants[0] if mutants else None

    def drive(outcomes: List[BuildResult]):
        fs = FakeScratch()
        pr = PlantedRunner(outcomes)
        rec = run_one(fs, srcs, m0, runner=pr)
        return rec, fs, pr

    if m0 is not None:
        # Planted always-survives control: both stages green through run_one.
        rec, fs, pr = drive([ok, ok])
        check("planted always-survives control classifies SURVIVED via run_one",
              rec["outcome"] == "SURVIVED" and pr.calls == 2, str(rec))
        check("run_one restores once and writes the mutant once",
              fs.restores == 1 and fs.mutants_written == [m0.mid],
              f"restores={fs.restores} wrote={fs.mutants_written}")
        check("run_one's module stage targets the mutated module",
              pr.targets[0] == [f"+{MODULES[m0.file_tag]}"] and
              pr.targets[1] == CLOSURE_TARGETS, str(pr.targets))
        # Planted always-killed control: closure stage red through run_one.
        rec, _, pr = drive([ok, killed])
        check("planted always-killed control classifies KILLED via run_one",
              rec["outcome"] == "KILLED" and pr.calls == 2, str(rec))
        check("planted always-killed control names the killing module",
              rec["killed_by"] == "LeanNative.Proofs.RealLCNFBridgeProofs", str(rec))
        check("planted always-killed control captures the first error line",
              bool(rec["first_error"]) and "unsolved goals" in str(rec["first_error"]),
              str(rec))
        # Planted stillborn control: module stage red, closure never runs.
        rec, _, pr = drive([stillborn])
        check("planted stillborn control classifies NOT_APPLICABLE and skips "
              "the closure stage", rec["outcome"] == "NOT_APPLICABLE" and
              pr.calls == 1, f"{rec} calls={pr.calls}")
        # Timeout and OOM are unmeasured, never kills (review F3/F4).
        rec, _, _ = drive([ok, timeout])
        check("planted timeout control classifies TIMEOUT (never a kill)",
              rec["outcome"] == "TIMEOUT", str(rec))
        rec, _, _ = drive([ok, oom_rc])
        check("planted OOM rc-137 control classifies INFRA (never a kill)",
              rec["outcome"] == "INFRA", str(rec))
        rec, _, _ = drive([ok, oom_text])
        check("planted 'exited with code 137' control classifies INFRA",
              rec["outcome"] == "INFRA", str(rec))
        rec, _, _ = drive([ok, infra_fail])
        check("planted infra control classifies INFRA (never a kill)",
              rec["outcome"] == "INFRA", str(rec))
        # A GREEN build whose output echoes a signature is a real SURVIVED
        # (review F4: signatures are only consulted on failed builds).
        rec, _, _ = drive([ok, green_with_sig])
        check("green build echoing an infra signature stays SURVIVED",
              rec["outcome"] == "SURVIVED", str(rec))
        # Review r2 F3: a FAILED build whose log carries a dependent module's
        # own `info:` output echoing a signature, beside a real proof error,
        # is a KILL — signatures are matched on error lines and the tail
        # block, never on the whole log.
        kill_with_dep_info = BuildResult(1, "\n".join([
            "info: LeanNative/Tests/HeapObjContract.lean:9:0: simulated",
            "info: heap pressure probe: out of memory path exercised",
            "✖ [12/44] Building LeanNative.Proofs.RealLCNFBridge.Scalar",
            "error: lean/LeanNative/Proofs/RealLCNFBridge/Scalar.lean:77:2: "
            "error: unsolved goals",
            "pad line 1", "pad line 2", "pad line 3", "pad line 4",
            "pad line 5", "error: build failed",
        ]), 2.0)
        rec, _, _ = drive([ok, kill_with_dep_info])
        check("failed build with a dependent module's infra-text info line "
              "stays KILLED",
              rec["outcome"] == "KILLED" and
              rec["killed_by"] == "LeanNative.Proofs.RealLCNFBridge.Scalar",
              str(rec))
        # A harness exception becomes an ERROR row, not an abort (review F6).
        err_rec = safe_run_one(RaisingScratch(), srcs, m0,
                               runner=PlantedRunner([ok, ok]))
        check("a harness exception becomes an ERROR row",
              err_rec["outcome"] == "ERROR" and
              "planted scratch failure" in str(err_rec["reason"]), str(err_rec))

    # The committed results artifact backs the CI sample's KILLED claims
    # (review F9): every pinned id must be recorded KILLED at the pinned shas.
    if RESULTS_PATH.exists():
        doc = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
        by_id = {r["id"]: r for r in doc.get("mutants", [])}
        missing = [mid for mid, exp in CI_SAMPLE
                   if by_id.get(mid, {}).get("outcome") != exp]
        check("every CI sample id is recorded KILLED in the committed results "
              "JSON", not missing, str(missing))
        stale = [rel for rel, sha in doc.get("files", {}).items()
                 if sha not in PINNED_SHA256.values()]
        check("committed results JSON was measured at the pinned source shas",
              not stale, str(stale))
    else:
        check("committed results JSON exists (scripts/"
              "proof_mutant_matrix_results.json)", False, "file missing")

    print(f"[self-test] {'OK' if not failures else 'FAILED'} "
          f"({len(failures)} failure(s))")
    return 0 if not failures else 1


def write_results(path: Path, results: List[Dict[str, object]],
                  srcs: Dict[str, str], commit: str) -> None:
    # Review F2: the recorded commit and toolchain are the MEASURED ones
    # (captured when the scratch worktrees were created), not re-read state.
    toolchain = git_show(ROOT, commit, "lean/lean-toolchain").strip()
    doc = {
        "schemaVersion": SCHEMA,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "measured_commit": commit,
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
    ap.add_argument("--jsonl", default="",
                    help="per-mutant progress JSONL (default: "
                         "h14-matrix-progress.jsonl in the repo root)")
    ap.add_argument("--resume", action="store_true",
                    help="reuse measured rows from the progress JSONL")
    ap.add_argument("--keep-scratch", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    commit = git(ROOT, "rev-parse", "HEAD")
    clean_errs = assert_sources_clean(ROOT, commit)
    srcs = read_sources_at(ROOT, commit)
    pin_errs = check_pins(srcs)
    mutants, errs = enumerate_mutants(srcs)
    if clean_errs or pin_errs or errs:
        for e in clean_errs + pin_errs + errs:
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

    jsonl_path = Path(args.jsonl) if args.jsonl else ROOT / "h14-matrix-progress.jsonl"
    print(f"[proof-mutant-matrix] running {len(selected)} mutant(s) at "
          f"{commit[:12]}, {min(max(1, args.workers), len(selected))} worker(s), "
          f"progress -> {jsonl_path}")
    results = run_matrix(selected, srcs, commit, max(1, args.workers),
                         args.timeout, args.keep_scratch, jsonl_path,
                         args.resume)
    summary = summarize(results)
    print(json.dumps(summary, indent=2))

    if args.json_out:
        write_results(Path(args.json_out), results, srcs, commit)

    rc = 0
    unmeasured = (summary["infra_unmeasured"] + summary["timeout_unmeasured"]
                  + summary["error_unmeasured"])
    if unmeasured:
        print(f"[proof-mutant-matrix] {unmeasured} unmeasured outcome(s) "
              f"(INFRA/TIMEOUT/ERROR): rerun with --resume", file=sys.stderr)
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
