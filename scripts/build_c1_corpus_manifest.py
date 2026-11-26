#!/usr/bin/env python3
"""Build / verify the Tier C1 upstream corpus manifest (`scripts/c1_corpus_manifest.json`).

Work-graph leaf **C1x** (`roadmap/HORIZONS.md`): "C1 corpus to 250 programs,
chosen by the matrix | corpus manifest | `--tier C1`".

Why this exists
---------------
The blocking `--tier C1` corpus was eight authored 3-way fixtures
(`C1_CORPUS_TESTS`); the roadmap asks for 250 upstream `leanprover/lean4`
run-suite programs chosen by the LCNF coverage matrix
(`scripts/lcnf_coverage.py`, committed results
`scripts/lcnf_coverage_results.json` @ `measured_source_commit 2d18487b`).
Nothing upstream is vendored: the corpus is provisioned at suite runtime
exactly like the Tier C2 external arm (pinned `repo_url` + `commit_sha`,
`git fetch --depth 1` into the `TURBO_LEAN_HOME` cache, stamp file,
fail-closed `BLOCKED_MISSING_DEPENDENCY` when absent). This script owns the
pin, the deterministic 250-program selection, and the manifest gate the suite
runs before executing the corpus.

Origin-path note (measured at the pin)
--------------------------------------
The roadmap names `lean4/tests/lean/run`. At the pinned revision
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, tag `v4.35.0`) that directory no
longer exists: upstream reorganized the test suite into "test piles"
(`tests/README.md` at the pin). The successor piles holding the historic
self-contained run tests are `tests/elab` (elaborate-and-verify, 3,214
`.lean` files) and `tests/compile` (compile-and-execute, 88 `.lean` files).
The manifest records each program's real origin path under those piles.

Honesty rules (matching `scripts/lcnf_coverage.py`)
---------------------------------------------------
- `matrixConstructs` entries are SYNTACTIC SELECTION MARKERS: regexes over the
  program source chosen so the corpus exercises the matrix's
  `lowered_unproved` and `rejected` rows. They are never represented as
  executed lowering; the executed classification is what
  `run_conformance_suite.py --tier C1` records per program when it runs
  `emit-lnir` (fail-closed nonzero exit = the rejected shape).
- `LetValue.fap.gf_simd` is excluded from the coverage targets: the matrix
  row itself records 0 hits across every measured corpus (Std/Init+C2, C1,
  con-leche), and the intrinsic whitelist has no syntactic surface in
  upstream test files. The exclusion is recorded in the manifest.
- The selection is deterministic (sorted enumeration, fixed quotas, greedy
  rounds); re-running `--write` against the pinned checkout reproduces the
  committed manifest byte for byte.
- Only import-free (self-contained) pile files are candidates: the suite leg
  elaborates each program standalone, and import-bearing files fail
  elaboration outright at the pin (measured 2026-11-26: the five
  tests/elab/bv_*.lean importing Std.Tactic.BVDecide), which the hardened leg
  records as `frontend_error`, never as an expected rejection.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import sys
import unittest
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "scripts" / "c1_corpus_manifest.json"
SCHEMA_VERSION = "turbo-lean-c1-corpus-v1"

# The pin. The tag's toolchain matches the repo pin (lean/lean-toolchain =
# leanprover/lean4:v4.35.0), so corpus programs elaborate under the same
# toolchain the suite's engines are built with. The elan-installed toolchain
# ships no tests/ directory, hence runtime provisioning of the source repo.
C1_UPSTREAM_REPO_URL = "https://github.com/leanprover/lean4"
C1_UPSTREAM_REV = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
C1_UPSTREAM_TAG = "v4.35.0"
C1_UPSTREAM_TOOLCHAIN = "leanprover/lean4:v4.35.0"
CORPUS_PILES = ("tests/compile", "tests/elab")
PROGRAM_COUNT = 250
# Keeps per-program `emit-lnir` elaboration bounded (measured ~0.4-0.5 s on
# import-free pile files; large files and heavy imports grow superlinearly).
MAX_PROGRAM_BYTES = 24_000

ORIGIN_NOTE = (
    "roadmap names lean4/tests/lean/run; at the pinned rev (tag v4.35.0) upstream has "
    "reorganized the suite into test piles (tests/README.md), and the successor piles for "
    "the self-contained run tests are tests/elab and tests/compile. Paths are recorded "
    "as they exist at the pin."
)
CATEGORIES_NOTE = (
    "matrixConstructs/emphasis are syntactic selection markers (regexes over program "
    "source), chosen to exercise the lowered_unproved and rejected rows of the LCNF "
    "coverage matrix; they are not executed-lowering measurements. The executed "
    "classification is recorded per program by run_conformance_suite.py --tier C1."
)

# Coverage targets: every `lowered_unproved` and `rejected` row of
# LCNF_CONSTRUCTOR_MATRIX_SPEC (scripts/lcnf_coverage.py), except the recorded
# exclusion below. (id, matrix status, syntactic detector).
_MULTI_DEF = "__multi_def__"  # sentinel: >= 2 top-level `def`s (local user call sites)
TARGET_CONSTRUCT_SPEC: tuple[tuple[str, str, str], ...] = (
    ("DeclValue.extern", "rejected", r"@\[extern"),
    ("Code.jp.recursive", "rejected", r"\blet\s+rec\b"),
    ("Code.fun", "rejected", r"(?:\bfun\b|λ)"),
    ("LetValue.lit.str", "rejected", r"\""),
    ("LetValue.fvar.app", "rejected", r"\(\s*\w[^)]*:\s*[^)]*(?:→|->)[^)]*\)"),
    (
        "LetValue.ctor.general",
        "rejected",
        r"\b(?:inductive|structure|Array|ByteArray|List|Option|String)\b|#\[",
    ),
    (
        "LetValue.fap.general",
        "rejected",
        r"\bpartial\s+def\b|\bmutual\b|\btermination_by\b|\bdecreasing_by\b",
    ),
    (
        "LetValue.pap",
        "rejected",
        r"\.(?:map|foldl|foldr|filter|any|all|mapM|forM)\b|\.find\?|\(·",
    ),
    ("LetValue.reset_reuse", "rejected", r"\.(?:set!|set|modify|push|pop)\b"),
    # R5: the width suffix is required; bare `Int` (arbitrary precision) is not
    # a signed fixed-width scalar and must not satisfy this detector.
    ("Type.signed_scalars", "rejected", r"\b(?:Int(?:8|16|32|64)|ISize)\b"),
    # L1 (81986e6a) deleted the pure-phase lowering these two rows named; the
    # matrix re-bins them as rejected (no impure LCNF form fails closed). Status
    # only: the detectors and their order, which drive selection, are unchanged.
    ("LetValue.proj", "rejected", r"\.(?:fst|snd|[12])\b"),
    ("LetValue.const", "rejected", r"\b[A-Z][A-Za-z0-9]*\.[a-z][A-Za-z0-9_!?']*"),
    ("LetValue.fap.local_call", "lowered_unproved", _MULTI_DEF),
)
EXCLUDED_TARGETS: dict[str, str] = {
    "LetValue.fap.gf_simd": (
        "GF(2^128)/BabyBear/Goldilocks SIMD intrinsic whitelist has no syntactic surface "
        "in upstream test files; the matrix row records 0 hits across Std/Init+C2, C1, "
        "and con-leche corpora."
    ),
}

# Roadmap-named emphasis ("closures, pap, letrec, Array/ByteArray sharing,
# signed Int*"): (marker, regex, quota). The build fills each quota up to
# availability and records the attained floor as `required`, which the gate
# re-checks against the program rows.
EMPHASIS_SPEC: tuple[tuple[str, str, int], ...] = (
    ("closures", r"(?:\bfun\b|λ)", 40),
    ("pap_partial_application", r"\.(?:map|foldl|foldr|filter)\b|\(·", 30),
    ("letrec", r"\blet\s+rec\b", 30),
    ("array_bytearray_sharing", r"\b(?:Array|ByteArray)\b", 30),
    ("signed_int_scalars", r"\b(?:Int(?:8|16|32|64)|ISize)\b", 30),
)

_IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s", re.M)
_DEF_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*def\s",
    re.M,
)


def _compiled_detectors() -> dict[str, Any]:
    out: dict[str, Any] = {}
    for cid, _status, pat in TARGET_CONSTRUCT_SPEC:
        out[cid] = _MULTI_DEF if pat == _MULTI_DEF else re.compile(pat)
    return out


_DETECTORS = _compiled_detectors()
_EMPHASIS = {name: re.compile(pat) for name, pat, _q in EMPHASIS_SPEC}
TARGET_STATUS = {cid: status for cid, status, _p in TARGET_CONSTRUCT_SPEC}


def detector_digest() -> str:
    """F3 (round 2): sha256 over everything that shapes candidate enumeration
    and selection (both spec tuples, the size bound, the import-free rule,
    the pile set). Recorded in the manifest and re-checked by the
    manifest-only gate, so a detector edit without `--write` fails the PR
    gate instead of only failing at nightly runtime."""
    payload = json.dumps(
        {
            "targetConstructSpec": [list(row) for row in TARGET_CONSTRUCT_SPEC],
            "emphasisSpec": [list(row) for row in EMPHASIS_SPEC],
            "maxProgramBytes": MAX_PROGRAM_BYTES,
            "importRe": _IMPORT_RE.pattern,
            "corpusPiles": list(CORPUS_PILES),
        },
        sort_keys=True,
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def matrix_constructs(text: str) -> list[str]:
    hits = []
    for cid, _status, _pat in TARGET_CONSTRUCT_SPEC:
        det = _DETECTORS[cid]
        if det == _MULTI_DEF:
            if len(_DEF_RE.findall(text)) >= 2:
                hits.append(cid)
        elif det.search(text):
            hits.append(cid)
    return hits


def emphasis_markers(text: str) -> list[str]:
    return [name for name, _p, _q in EMPHASIS_SPEC if _EMPHASIS[name].search(text)]


def corpus_cache_dir() -> Path:
    raw_home = os.environ.get("TURBO_LEAN_HOME", "").strip()
    base = Path(raw_home) if raw_home else Path.home() / ".cache" / "turbo-lean"
    return base / "c1-upstream" / f"lean4-{C1_UPSTREAM_REV[:12]}"


def enumerate_candidates(corpus_root: Path) -> list[dict[str, Any]]:
    cands: list[dict[str, Any]] = []
    for pile in CORPUS_PILES:
        pile_dir = corpus_root / pile
        if not pile_dir.is_dir():
            raise FileNotFoundError(f"corpus pile missing: {pile_dir}")
        for fp in sorted(pile_dir.glob("*.lean")):
            raw = fp.read_bytes()
            if len(raw) > MAX_PROGRAM_BYTES:
                continue
            text = raw.decode("utf-8", errors="replace")
            if _IMPORT_RE.search(text) is not None:
                # The suite leg elaborates each program standalone, so only
                # self-contained (import-free) pile files are candidates.
                # Measured at the pin: import-bearing files (the five
                # tests/elab/bv_*.lean importing Std.Tactic.BVDecide) fail
                # elaboration outright, which the hardened leg records as
                # frontend_error, not as an expected rejection.
                continue
            cands.append(
                {
                    "path": f"{pile}/{fp.name}",
                    "bytes": len(raw),
                    "sha256": hashlib.sha256(raw).hexdigest(),
                    "importFree": _IMPORT_RE.search(text) is None,
                    "matrixConstructs": matrix_constructs(text),
                    "emphasis": emphasis_markers(text),
                }
            )
    return cands


def select_programs(
    cands: list[dict[str, Any]], program_count: int, quotas: dict[str, int]
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Deterministic greedy selection: emphasis quotas, then target-construct
    coverage, then fill by construct breadth. Prefers import-free, small files."""
    ordered = sorted(cands, key=lambda c: (not c["importFree"], c["bytes"], c["path"]))
    chosen: dict[str, dict[str, Any]] = {}
    attained: dict[str, int] = {}

    def add(c: dict[str, Any]) -> None:
        chosen.setdefault(c["path"], c)

    for name, _pat, _q in EMPHASIS_SPEC:
        quota = quotas[name]
        available = [c for c in ordered if name in c["emphasis"]]
        want = min(quota, len(available), program_count)
        have = sum(1 for c in chosen.values() if name in c["emphasis"])
        for c in available:
            if have >= want or len(chosen) >= program_count:
                break
            if c["path"] not in chosen:
                add(c)
                have += 1
        attained[name] = min(want, have)

    for cid, _status, _pat in TARGET_CONSTRUCT_SPEC:
        if any(cid in c["matrixConstructs"] for c in chosen.values()):
            continue
        for c in ordered:
            if cid in c["matrixConstructs"] and c["path"] not in chosen:
                add(c)
                break

    # R6: never pad the corpus with a candidate carrying no matrix constructs;
    # every selected program must exercise at least one targeted matrix row.
    fill = sorted(
        (c for c in ordered if c["path"] not in chosen and c["matrixConstructs"]),
        key=lambda c: (not c["importFree"], -len(c["matrixConstructs"]), c["bytes"], c["path"]),
    )
    for c in fill:
        if len(chosen) >= program_count:
            break
        add(c)

    if len(chosen) != program_count:
        raise RuntimeError(
            f"selection produced {len(chosen)} programs; {program_count} required "
            f"(candidates: {len(cands)})"
        )
    return sorted(chosen.values(), key=lambda c: c["path"]), attained


def build_manifest(
    corpus_root: Path,
    program_count: int = PROGRAM_COUNT,
    quotas: dict[str, int] | None = None,
) -> dict[str, Any]:
    quotas = quotas if quotas is not None else {name: q for name, _p, q in EMPHASIS_SPEC}
    programs, attained = select_programs(enumerate_candidates(corpus_root), program_count, quotas)
    emphasis_counts = {
        name: sum(1 for c in programs if name in c["emphasis"]) for name, _p, _q in EMPHASIS_SPEC
    }
    return {
        "schemaVersion": SCHEMA_VERSION,
        "detectorDigest": detector_digest(),
        "pin": {
            "repoUrl": C1_UPSTREAM_REPO_URL,
            "rev": C1_UPSTREAM_REV,
            "tag": C1_UPSTREAM_TAG,
            "toolchain": C1_UPSTREAM_TOOLCHAIN,
        },
        "originNote": ORIGIN_NOTE,
        "categoriesNote": CATEGORIES_NOTE,
        "matrixSource": {
            "spec": "scripts/lcnf_coverage.py",
            "committedResults": "scripts/lcnf_coverage_results.json",
            "measuredSourceCommit": "2d18487bfecacada542884c868953424bfc75161",
        },
        "targetConstructs": dict(TARGET_STATUS),
        "excludedTargets": dict(EXCLUDED_TARGETS),
        "emphasis": {
            name: {"pattern": pat, "count": emphasis_counts[name], "required": attained[name]}
            for name, pat, _q in EMPHASIS_SPEC
        },
        "programCount": len(programs),
        "programs": programs,
    }


def verify_manifest(
    manifest_path: Path = MANIFEST_PATH,
    corpus_root: Path | None = None,
    expect_program_count: int = PROGRAM_COUNT,
    quotas: dict[str, int] | None = None,
) -> dict[str, Any]:
    """The C1x manifest gate. Manifest-only checks always run; with
    `corpus_root` every program is re-read from the pinned checkout (sha256,
    recomputed matrix constructs AND emphasis markers must match), and each
    emphasis `required` floor is checked against min(quota, measured
    available-at-the-pin) rather than the manifest's own recorded value (R6).
    Returns `{"ok": bool, "reasons": [...]}`."""
    quotas = quotas if quotas is not None else {name: q for name, _p, q in EMPHASIS_SPEC}
    reasons: list[str] = []
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as err:
        return {"ok": False, "reasons": [f"manifest unreadable: {err}"], "programCount": 0}

    if manifest.get("schemaVersion") != SCHEMA_VERSION:
        reasons.append(f"schemaVersion != {SCHEMA_VERSION!r}")
    if manifest.get("detectorDigest") != detector_digest():
        reasons.append(
            "detectorDigest does not match the current detector set (TARGET_CONSTRUCT_SPEC, "
            "EMPHASIS_SPEC, MAX_PROGRAM_BYTES, import-free rule, CORPUS_PILES); regenerate with --write"
        )
    pin = manifest.get("pin", {})
    for key, want in (
        ("repoUrl", C1_UPSTREAM_REPO_URL),
        ("rev", C1_UPSTREAM_REV),
        ("toolchain", C1_UPSTREAM_TOOLCHAIN),
    ):
        if pin.get(key) != want:
            reasons.append(f"pin.{key} is {pin.get(key)!r}, expected {want!r}")
    if manifest.get("targetConstructs") != dict(TARGET_STATUS):
        reasons.append("targetConstructs do not match the matrix target rows this script pins")
    if set(manifest.get("excludedTargets", {})) != set(EXCLUDED_TARGETS):
        reasons.append("excludedTargets do not match the recorded exclusion set")

    programs = manifest.get("programs", [])
    count = manifest.get("programCount")
    if count != expect_program_count or len(programs) != expect_program_count:
        reasons.append(
            f"program count mismatch: programCount={count}, rows={len(programs)}, "
            f"required={expect_program_count}"
        )
    paths = [p.get("path", "") for p in programs]
    if len(set(paths)) != len(paths):
        reasons.append("duplicate program paths")
    for p in programs:
        path = p.get("path", "")
        if not any(path.startswith(pile + "/") for pile in CORPUS_PILES):
            reasons.append(f"{path!r} is outside the corpus piles {CORPUS_PILES}")
            break
        if not re.fullmatch(r"[0-9a-f]{64}", p.get("sha256", "")):
            reasons.append(f"{path!r} has no well-formed sha256")
            break
        if p.get("importFree") is not True:
            reasons.append(f"{path!r} is not import-free; the leg elaborates programs standalone")
            break
        if not p.get("matrixConstructs") or not set(p["matrixConstructs"]) <= set(TARGET_STATUS):
            reasons.append(f"{path!r} has empty or unknown matrixConstructs")
            break

    covered = set()
    for p in programs:
        covered.update(p.get("matrixConstructs", []))
    missing = [cid for cid in TARGET_STATUS if cid not in covered]
    if missing:
        reasons.append(f"matrix constructs with no covering program: {missing}")

    available: dict[str, int] | None = None
    if corpus_root is not None and not reasons:
        try:
            cands = enumerate_candidates(corpus_root)
            available = {
                name: sum(1 for c in cands if name in c["emphasis"]) for name, _p, _q in EMPHASIS_SPEC
            }
        except (FileNotFoundError, OSError) as err:
            reasons.append(f"cannot measure emphasis availability at the pin: {err}")

    for name, pat, _q in EMPHASIS_SPEC:
        rec = manifest.get("emphasis", {}).get(name, {})
        actual = sum(1 for p in programs if name in p.get("emphasis", []))
        if rec.get("pattern") != pat:
            # F3 (round 2): the recorded pattern is compared with the spec, so
            # a stale manifest cannot ride its own recorded detector text.
            reasons.append(f"emphasis {name!r}: recorded pattern differs from EMPHASIS_SPEC")
        elif rec.get("count") != actual:
            reasons.append(f"emphasis {name!r}: recorded count {rec.get('count')} != rows {actual}")
        elif available is not None:
            # R6: the floor is measured, never trusted from the manifest.
            floor = min(quotas[name], available[name], expect_program_count)
            if rec.get("required") != floor:
                reasons.append(
                    f"emphasis {name!r}: recorded required {rec.get('required')} != "
                    f"min(quota {quotas[name]}, measured available {available[name]}) = {floor}"
                )
            elif actual < floor:
                reasons.append(f"emphasis {name!r}: rows {actual} below measured floor {floor}")
        elif actual < int(rec.get("required", 0)):
            reasons.append(f"emphasis {name!r}: rows {actual} below required {rec.get('required')}")

    verified_files = 0
    if corpus_root is not None and not reasons:
        for p in programs:
            fp = corpus_root / p["path"]
            try:
                raw = fp.read_bytes()
            except OSError as err:
                reasons.append(f"{p['path']!r} unreadable at the pin: {err}")
                break
            if hashlib.sha256(raw).hexdigest() != p["sha256"]:
                reasons.append(f"{p['path']!r} sha256 does not match the pinned checkout")
                break
            text = raw.decode("utf-8", errors="replace")
            if matrix_constructs(text) != p["matrixConstructs"]:
                reasons.append(f"{p['path']!r} matrixConstructs drifted from the detectors")
                break
            # R6: emphasis markers are recomputed from source too, so a stale
            # or hand-edited emphasis list cannot ride a matching sha.
            if emphasis_markers(text) != p.get("emphasis", []):
                reasons.append(f"{p['path']!r} emphasis markers drifted from the detectors")
                break
            verified_files += 1

    return {
        "ok": not reasons,
        "reasons": reasons,
        "programCount": len(programs),
        "coveredTargets": sorted(covered),
        "shaVerifiedFiles": verified_files,
        "corpusRoot": str(corpus_root) if corpus_root is not None else None,
    }


def write_manifest_gated(
    corpus_root: Path,
    manifest_path: Path,
    program_count: int = PROGRAM_COUNT,
    quotas: dict[str, int] | None = None,
) -> int:
    """R6: build the manifest, write it to a sibling temp file, run
    verify_manifest on it against the pinned checkout, and only then replace
    the committed manifest. A failed gate refuses the write (exit 2) and
    leaves the committed manifest untouched."""
    manifest = build_manifest(corpus_root, program_count=program_count, quotas=quotas)
    tmp_path = manifest_path.with_name(manifest_path.name + ".tmp")
    tmp_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    gate = verify_manifest(
        tmp_path, corpus_root=corpus_root, expect_program_count=program_count, quotas=quotas
    )
    if gate.get("ok") is not True:
        print("[c1-corpus] --write refused: the freshly built manifest fails its own gate", file=sys.stderr)
        for reason in gate.get("reasons", []):
            print(f"  [reason] {reason}", file=sys.stderr)
        tmp_path.unlink()
        return 2
    os.replace(tmp_path, manifest_path)
    print(f"[c1-corpus] wrote {manifest_path} ({manifest['programCount']} programs; gate PASSED pre-write)")
    return 0


# --------------------------- self-test ---------------------------

_SYNTH_FILES = {
    # Every target construct is covered by the union of these snippets.
    "tests/elab/synth_extern.lean": '@[extern "c_magic"] opaque magicExt : UInt64 → UInt64\n',
    "tests/elab/synth_hof.lean": "def hof (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x\n",
    "tests/elab/synth_letrec.lean": 'def go (n : Nat) : Nat :=\n  let rec aux (k : Nat) := fun m => k + m\n  aux n 1\ndef s := "x"\n',
    "tests/elab/synth_rec.lean": "partial def ping (x : UInt64) : UInt64 := ping x\nmutual\nend\n",
    "tests/elab/synth_heap.lean": "inductive T where | mk (a : Array Nat)\ndef arr := #[1, 2]\ndef upd := (#[1]).set! 0 2\ndef m := [1].map (· + 1)\n",
    "tests/elab/synth_scalar.lean": "def one : Nat := Nat.succ 0\ndef two := one\ndef pr := (1, 2).fst\ndef si : Int8 := 1\n",
    "tests/compile/synth_main.lean": 'def main : IO Unit := IO.println "hi"\n',
}


class C1CorpusManifestSelfTest(unittest.TestCase):
    def _synth_corpus(self, tmp: Path) -> Path:
        for rel, text in _SYNTH_FILES.items():
            fp = tmp / rel
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_text(text, encoding="utf-8")
        return tmp

    def _small_manifest(self, tmp: Path) -> dict[str, Any]:
        root = self._synth_corpus(tmp)
        quotas = {name: 1 for name, _p, _q in EMPHASIS_SPEC}
        return build_manifest(root, program_count=len(_SYNTH_FILES), quotas=quotas)

    def test_detectors_match_planted_snippets(self):
        union: set[str] = set()
        for text in _SYNTH_FILES.values():
            union.update(matrix_constructs(text))
        self.assertEqual(union, set(TARGET_STATUS), "synthetic corpus must cover every target")
        self.assertNotIn("Type.signed_scalars", matrix_constructs("def f (x : UInt64) : UInt64 := x\n"))
        # R5: the signed-scalar detector requires the width suffix; bare `Int`
        # is arbitrary precision, not a signed fixed-width scalar.
        self.assertNotIn("Type.signed_scalars", matrix_constructs("def f (x : Int) := x\n"))
        self.assertNotIn("signed_int_scalars", emphasis_markers("def f (x : Int) := x\n"))
        self.assertIn("Type.signed_scalars", matrix_constructs("def g (y : Int32) := y\n"))
        self.assertIn("signed_int_scalars", emphasis_markers("def g (y : Int32) := y\n"))
        self.assertNotIn("DeclValue.extern", matrix_constructs("def f := 1\n"))
        self.assertIn("LetValue.fap.local_call", matrix_constructs("def a := 1\ndef b := a\n"))
        self.assertNotIn("LetValue.fap.local_call", matrix_constructs("def a := 1\n"))

    def test_target_rows_match_lcnf_coverage_matrix(self):
        src = (ROOT / "scripts" / "lcnf_coverage.py").read_text(encoding="utf-8")
        m = re.search(r"LCNF_CONSTRUCTOR_MATRIX_SPEC[^=]*=\s*(\(.*?\n\))\n", src, re.S)
        self.assertIsNotNone(m, "LCNF_CONSTRUCTOR_MATRIX_SPEC not found")
        spec = ast.literal_eval(m.group(1))
        by_id = {row["id"]: row["status"] for row in spec}
        for cid, status in TARGET_STATUS.items():
            self.assertEqual(by_id.get(cid), status, f"matrix drift on {cid}")
        for cid in EXCLUDED_TARGETS:
            self.assertEqual(by_id.get(cid), "lowered_unproved", f"exclusion drift on {cid}")
        unproved_or_rejected = {
            rid for rid, st in by_id.items() if st in ("lowered_unproved", "rejected")
        }
        self.assertEqual(
            unproved_or_rejected,
            set(TARGET_STATUS) | set(EXCLUDED_TARGETS),
            "target set must equal the matrix's lowered_unproved+rejected rows minus recorded exclusions",
        )

    def test_gate_green_then_red_on_planted_bad_manifests(self):
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_selftest_") as tmp:
            root = Path(tmp)
            manifest = self._small_manifest(root)
            mp = root / "manifest.json"
            n = len(_SYNTH_FILES)

            mp.write_text(json.dumps(manifest), encoding="utf-8")
            green = verify_manifest(mp, corpus_root=root, expect_program_count=n)
            self.assertTrue(green["ok"], green["reasons"])
            self.assertEqual(green["shaVerifiedFiles"], n)

            bad_count = dict(manifest, programCount=n + 1)
            mp.write_text(json.dumps(bad_count), encoding="utf-8")
            self.assertFalse(verify_manifest(mp, expect_program_count=n)["ok"])

            bad_sha = json.loads(json.dumps(manifest))
            bad_sha["programs"][0]["sha256"] = "0" * 64
            mp.write_text(json.dumps(bad_sha), encoding="utf-8")
            red = verify_manifest(mp, corpus_root=root, expect_program_count=n)
            self.assertFalse(red["ok"])
            self.assertTrue(any("sha256" in r for r in red["reasons"]), red["reasons"])

            # F3 (round 2): a detector edit without --write must fail the
            # manifest-only gate through the recorded detectorDigest...
            bad_digest = json.loads(json.dumps(manifest))
            bad_digest["detectorDigest"] = "0" * 64
            mp.write_text(json.dumps(bad_digest), encoding="utf-8")
            red3 = verify_manifest(mp, expect_program_count=n)
            self.assertFalse(red3["ok"])
            self.assertTrue(any("detectorDigest" in r for r in red3["reasons"]), red3["reasons"])

            # ...and through the per-emphasis recorded pattern vs EMPHASIS_SPEC.
            bad_pat = json.loads(json.dumps(manifest))
            bad_pat["emphasis"]["closures"]["pattern"] = r"\bfun\b"
            mp.write_text(json.dumps(bad_pat), encoding="utf-8")
            red4 = verify_manifest(mp, expect_program_count=n)
            self.assertFalse(red4["ok"])
            self.assertTrue(any("pattern" in r for r in red4["reasons"]), red4["reasons"])

            bad_cov = json.loads(json.dumps(manifest))
            for row in bad_cov["programs"]:
                row["matrixConstructs"] = [
                    c for c in row["matrixConstructs"] if c != "DeclValue.extern"
                ]
            bad_cov["programs"] = [p for p in bad_cov["programs"] if p["matrixConstructs"]]
            bad_cov["programCount"] = len(bad_cov["programs"])
            mp.write_text(json.dumps(bad_cov), encoding="utf-8")
            red2 = verify_manifest(mp, expect_program_count=bad_cov["programCount"])
            self.assertFalse(red2["ok"])
            self.assertTrue(any("no covering program" in r for r in red2["reasons"]), red2["reasons"])

    def test_import_bearing_files_are_not_candidates(self):
        # The leg elaborates each program standalone; a file importing beyond
        # the prelude (measured: the five tests/elab/bv_*.lean importing
        # Std.Tactic.BVDecide all fail elaboration outright at the pin) is not
        # a self-contained run test and never enters the candidate set.
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_imp_") as tmp:
            root = self._synth_corpus(Path(tmp))
            (root / "tests/elab/synth_imports.lean").write_text(
                "import Std.Tactic.BVDecide\ndef si2 : Int8 := 2\n", encoding="utf-8"
            )
            paths = [c["path"] for c in enumerate_candidates(root)]
            self.assertNotIn("tests/elab/synth_imports.lean", paths)
            self.assertIn("tests/elab/synth_scalar.lean", paths)

    def test_fill_step_skips_constructless_candidates(self):
        # R6: the fill step never pads the corpus with a candidate carrying no
        # matrix constructs; a program_count reachable only by padding raises.
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_fill_") as tmp:
            root = self._synth_corpus(Path(tmp))
            (root / "tests/elab/synth_constructless.lean").write_text(
                "-- no matrix constructs and no emphasis markers in this file\n",
                encoding="utf-8",
            )
            quotas = {name: 1 for name, _p, _q in EMPHASIS_SPEC}
            with self.assertRaises(RuntimeError):
                build_manifest(root, program_count=len(_SYNTH_FILES) + 1, quotas=quotas)

    def test_gate_checks_required_against_measured_floor(self):
        # R6: with a corpus root the gate recomputes each emphasis floor as
        # min(quota, measured available) instead of trusting the manifest's
        # own recorded `required` value.
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_floor_") as tmp:
            root = Path(tmp)
            manifest = self._small_manifest(root)
            mp = root / "manifest.json"
            lowered = json.loads(json.dumps(manifest))
            lowered["emphasis"]["closures"]["required"] = 0
            mp.write_text(json.dumps(lowered), encoding="utf-8")
            red = verify_manifest(mp, corpus_root=root, expect_program_count=len(_SYNTH_FILES))
            self.assertFalse(red["ok"])
            self.assertTrue(
                any("closures" in r and "required" in r for r in red["reasons"]), red["reasons"]
            )

    def test_gate_recomputes_emphasis_markers_from_source(self):
        # R6: the per-file corpus pass recomputes emphasis markers from
        # program source, not only matrixConstructs.
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_emph_") as tmp:
            root = Path(tmp)
            manifest = self._small_manifest(root)
            mp = root / "manifest.json"
            quotas = {name: 1 for name, _p, _q in EMPHASIS_SPEC}
            quotas["pap_partial_application"] = 0
            tampered = json.loads(json.dumps(manifest))
            for row in tampered["programs"]:
                row["emphasis"] = [e for e in row["emphasis"] if e != "pap_partial_application"]
            tampered["emphasis"]["pap_partial_application"]["count"] = 0
            tampered["emphasis"]["pap_partial_application"]["required"] = 0
            mp.write_text(json.dumps(tampered), encoding="utf-8")
            red = verify_manifest(
                mp, corpus_root=root, expect_program_count=len(_SYNTH_FILES), quotas=quotas
            )
            self.assertFalse(red["ok"])
            self.assertTrue(any("emphasis" in r and "drifted" in r for r in red["reasons"]), red["reasons"])

    def test_write_refuses_on_failed_gate(self):
        # R6: --write verifies the freshly built manifest before replacing the
        # committed one and refuses (exit 2, no write) on a failed gate.
        import tempfile
        from unittest import mock

        with tempfile.TemporaryDirectory(prefix="c1x_write_") as tmp:
            root = self._synth_corpus(Path(tmp))
            out = Path(tmp) / "out" / "manifest.json"
            out.parent.mkdir()
            quotas = {name: 1 for name, _p, _q in EMPHASIS_SPEC}
            rc = write_manifest_gated(root, out, program_count=len(_SYNTH_FILES), quotas=quotas)
            self.assertEqual(rc, 0)
            self.assertTrue(out.is_file())
            before = out.read_bytes()
            with mock.patch.object(
                sys.modules[__name__],
                "verify_manifest",
                return_value={"ok": False, "reasons": ["planted gate failure"], "programCount": 0},
            ):
                rc = write_manifest_gated(root, out, program_count=len(_SYNTH_FILES), quotas=quotas)
            self.assertEqual(rc, 2)
            self.assertEqual(out.read_bytes(), before, "a refused --write must not touch the manifest")
            self.assertFalse(list(out.parent.glob("*.tmp")), "a refused --write must clean its temp file")

    def test_selection_is_deterministic(self):
        import tempfile

        with tempfile.TemporaryDirectory(prefix="c1x_det_") as tmp:
            a = self._small_manifest(Path(tmp))
            b = self._small_manifest(Path(tmp))
            self.assertEqual(json.dumps(a, sort_keys=True), json.dumps(b, sort_keys=True))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the committed manifest from the pinned checkout")
    parser.add_argument("--verify", action="store_true", help="Run the manifest gate (count, pin, coverage; shas when --corpus-root resolves)")
    parser.add_argument("--self-test", action="store_true", help="Run the in-module unit tests (synthetic corpus; no network)")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--manifest", default=str(MANIFEST_PATH))
    parser.add_argument(
        "--corpus-root",
        default="auto",
        help="Pinned lean4 checkout (default `auto`: the TURBO_LEAN_HOME c1-upstream cache; `none` for manifest-only verify)",
    )
    args = parser.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(C1CorpusManifestSelfTest)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1

    if args.corpus_root == "none":
        corpus_root = None
    elif args.corpus_root == "auto":
        corpus_root = corpus_cache_dir() if corpus_cache_dir().is_dir() else None
    else:
        corpus_root = Path(args.corpus_root)

    if args.write:
        if corpus_root is None or not corpus_root.is_dir():
            print(
                f"[c1-corpus] cannot --write: pinned checkout not provisioned at {corpus_cache_dir()}",
                file=sys.stderr,
            )
            return 2
        return write_manifest_gated(corpus_root, Path(args.manifest))

    if args.verify:
        report = verify_manifest(Path(args.manifest), corpus_root=corpus_root)
        if args.json:
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            print(
                f"[c1-corpus] manifest gate: {'PASSED' if report['ok'] else 'FAILED'}; "
                f"programs={report['programCount']}; shaVerifiedFiles={report['shaVerifiedFiles'] if 'shaVerifiedFiles' in report else 0}; "
                f"corpusRoot={report.get('corpusRoot')}"
            )
            for reason in report["reasons"]:
                print(f"  [reason] {reason}")
        return 0 if report["ok"] else 1

    parser.error("one of --write / --verify / --self-test is required")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
