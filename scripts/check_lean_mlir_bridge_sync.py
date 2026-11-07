#!/usr/bin/env python3
"""Stage 2C: Exact AST/Evaluator Synchronization & Upstream Pin Gate for `verification/lean-mlir-bridge/`.

Verifies:
1. `verification/lean-mlir-bridge/LeanNative/Backend/{TargetIR.lean,LLVMAst/Syntax.lean,LLVMAst/Eval.lean}`
   are byte-identical to `lean/LeanNative/Backend/{TargetIR.lean,LLVMAst/Syntax.lean,LLVMAst/Eval.lean}`
   (preventing any drift or shadow divergence between the main `LeanNative` compiler and the
   `opencompl/lean-mlir` bisimulation package).
2. `verification/lean-mlir-bridge/SSA/Projects/InstCombine/{ForStd.lean,LLVM/SimpSet.lean}` match the
   exact SHA-256 digests of `opencompl/lean-mlir` commit `b8c4a771319a044854a4bbb49b8821381ef86ff8`.
3. `verification/lean-mlir-bridge/lakefile.toml` pins `opencompl/lean-mlir` at commit
   `b8c4a771319a044854a4bbb49b8821381ef86ff8` (`subDir = "LeanMLIR"`), and `LeanMLIRBridge` contains
   zero `sorry`, `admit`, `axiom`, `native_decide`, or `trustCompiler` tokens.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent.parent
BRIDGE_DIR = ROOT_DIR / "verification" / "lean-mlir-bridge"

PINNED_LEAN_MLIR_REV = "b8c4a771319a044854a4bbb49b8821381ef86ff8"
PINNED_SSA_SHAS = {
    "SSA/Projects/InstCombine/ForStd.lean": "501e7dcba9deade04ee6c979a387fe2bee49768bc3e9d18aa39b0de690a38488",
    "SSA/Projects/InstCombine/LLVM/SimpSet.lean": "1b439d5d23fb6c82aa2942efc0a559ca829da46c3c74b36137a362310b046220",
}

MIRRORED_FILES = (
    "LeanNative/Backend/TargetIR.lean",
    "LeanNative/Backend/LLVMAst/Syntax.lean",
    "LeanNative/Backend/LLVMAst/Eval.lean",
)

# Pre-filter scan outside Lean comments; kernel-level enforcement is `#verify_lean_mlir_bridge_axioms`
# (`Lean.collectAxioms` in `LeanMLIRBridge.lean`).
FORBIDDEN_PROOF_TOKENS = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|trustCompiler|ofReduceBool)\b",
    re.M,
)


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    depth = 0
    in_str = False
    i = 0
    while i < len(text):
        if depth == 0 and not in_str and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        elif not in_str and text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif in_str:
            if text[i] == "\\" and i + 1 < len(text):
                out.append("  ")
                i += 2
            elif text[i] == '"':
                in_str = False
                out.append('"')
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text[i] == '"':
            in_str = True
            out.append('"')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def check_bridge_tree(root_dir: Path, sync_mirrors: bool = False) -> dict[str, object]:
    lean_root = root_dir / "lean"
    bridge_root = root_dir / "verification" / "lean-mlir-bridge"
    errors: list[str] = []

    if not bridge_root.is_dir():
        return {"ok": False, "errors": [f"Missing bridge directory: {bridge_root}"]}

    # 1. Exact byte-identity of mirrored LLVMAst & TargetIR definitions
    mirror_digests: dict[str, str] = {}
    for rel in MIRRORED_FILES:
        src = lean_root / rel
        dst = bridge_root / rel
        if not src.is_file():
            errors.append(f"Missing canonical file: {src}")
            continue
        if sync_mirrors:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
        if not dst.is_file():
            errors.append(f"Missing mirrored bridge file: {dst}")
            continue
        s_sha = sha256_file(src)
        d_sha = sha256_file(dst)
        if s_sha != d_sha:
            errors.append(
                f"Drift detected in {rel}: lean={s_sha[:16]} != bridge={d_sha[:16]} "
                "(run `python3 scripts/check_lean_mlir_bridge_sync.py --sync`)"
            )
        mirror_digests[rel] = s_sha

    # 2. Exact upstream SHA-256 verification of the 2 minimal SSA support files
    for rel, expected_sha in PINNED_SSA_SHAS.items():
        f = bridge_root / rel
        if not f.is_file():
            errors.append(f"Missing pinned upstream SSA file: {f}")
            continue
        actual = sha256_file(f)
        if actual != expected_sha:
            errors.append(
                f"Upstream SSA SHA mismatch for {rel}: got {actual}, expected {expected_sha}"
            )

    # 3. Verify lakefile.toml (and lake-manifest.json if present) pin opencompl/lean-mlir at PINNED_LEAN_MLIR_REV
    lakefile = bridge_root / "lakefile.toml"
    if not lakefile.is_file():
        errors.append(f"Missing {lakefile}")
    else:
        lf_txt = lakefile.read_text(encoding="utf-8")
        if "https://github.com/opencompl/lean-mlir.git" not in lf_txt:
            errors.append("lakefile.toml missing https://github.com/opencompl/lean-mlir.git")
        if PINNED_LEAN_MLIR_REV not in lf_txt:
            errors.append(f"lakefile.toml missing pinned rev {PINNED_LEAN_MLIR_REV}")
        if 'subDir = "LeanMLIR"' not in lf_txt:
            errors.append('lakefile.toml missing subDir = "LeanMLIR"')

    manifest = bridge_root / "lake-manifest.json"
    if not manifest.is_file():
        errors.append(f"Missing committed {manifest}")
    else:
        try:
            mf = json.loads(manifest.read_text(encoding="utf-8"))
            pkgs = {p.get("name"): p for p in mf.get("packages", [])}
            lm_pkg = pkgs.get("LeanMLIR")
            if not lm_pkg:
                errors.append("lake-manifest.json missing LeanMLIR package")
            elif lm_pkg.get("rev") != PINNED_LEAN_MLIR_REV:
                errors.append(
                    f"lake-manifest.json LeanMLIR rev mismatch: {lm_pkg.get('rev')} != {PINNED_LEAN_MLIR_REV}"
                )
            cli_pkg = pkgs.get("Cli")
            if not cli_pkg or "mhuisi/lean4-cli" not in str(cli_pkg.get("url", "")):
                errors.append(
                    "lake-manifest.json Cli package must point to reachable https://github.com/mhuisi/lean4-cli.git"
                )
        except Exception as exc:
            errors.append(f"Invalid lake-manifest.json: {exc}")

    # 4. Scan bridge proof files for forbidden tokens (outside comments) and axiom audit gate
    root_bridge_lean = bridge_root / "LeanMLIRBridge.lean"
    if root_bridge_lean.is_file():
        rb_raw = root_bridge_lean.read_text(encoding="utf-8")
        if "#verify_lean_mlir_bridge_axioms" not in strip_lean_comments_and_strings(rb_raw):
            errors.append("LeanMLIRBridge.lean missing `#verify_lean_mlir_bridge_axioms` gate")
        bridged_refs = re.findall(
            r"``LeanMLIRBridge\.[A-Za-z0-9_?']+",
            strip_lean_comments_and_strings(rb_raw),
        )
        if len(bridged_refs) < 30:
            errors.append(
                f"LeanMLIRBridge.lean audits only {len(bridged_refs)} bridged theorems (expected >= 30)"
            )
    proof_files = [
        root_bridge_lean,
        *sorted((bridge_root / "LeanMLIRBridge").rglob("*.lean")),
    ]
    if len(proof_files) < 2:
        errors.append("Expected LeanMLIRBridge.lean and LeanMLIRBridge/*.lean proof modules")
    for pf in proof_files:
        if not pf.is_file():
            errors.append(f"Missing proof file: {pf}")
            continue
        stripped = strip_lean_comments_and_strings(pf.read_text(encoding="utf-8"))
        m = FORBIDDEN_PROOF_TOKENS.search(stripped)
        if m:
            errors.append(f"Forbidden token `{m.group(0).strip()}` in {pf.relative_to(root_dir)}")

    return {
        "ok": len(errors) == 0,
        "pinned_lean_mlir_rev": PINNED_LEAN_MLIR_REV,
        "mirrored_files": mirror_digests,
        "proof_files_checked": len(proof_files),
        "errors": errors,
    }


class SelfTests(unittest.TestCase):
    def test_live_repo_passes(self) -> None:
        rep = check_bridge_tree(ROOT_DIR)
        self.assertTrue(rep["ok"], rep)

    def test_detects_mirror_drift_and_sorry(self) -> None:
        with tempfile.TemporaryDirectory(prefix="mlir-sync-test-") as tmp:
            root = Path(tmp)
            for rel in MIRRORED_FILES:
                p1 = root / "lean" / rel
                p2 = root / "verification" / "lean-mlir-bridge" / rel
                p1.parent.mkdir(parents=True, exist_ok=True)
                p2.parent.mkdir(parents=True, exist_ok=True)
                p1.write_text("def x := 1\n", encoding="utf-8")
                p2.write_text("def x := 2\n", encoding="utf-8")
            for rel in PINNED_SSA_SHAS:
                src = BRIDGE_DIR / rel
                dst = root / "verification" / "lean-mlir-bridge" / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            shutil.copy2(
                BRIDGE_DIR / "lakefile.toml",
                root / "verification" / "lean-mlir-bridge" / "lakefile.toml",
            )
            shutil.copy2(
                BRIDGE_DIR / "lake-manifest.json",
                root / "verification" / "lean-mlir-bridge" / "lake-manifest.json",
            )
            b_root = root / "verification" / "lean-mlir-bridge"
            (b_root / "LeanMLIRBridge").mkdir(parents=True, exist_ok=True)
            (b_root / "LeanMLIRBridge.lean").write_text("import LeanMLIRBridge.Bisim\n")
            (b_root / "LeanMLIRBridge" / "Bisim.lean").write_text(
                'def msg := "string with -- sorry and axiom"\nprivate noncomputable axiom sneaky : False\n',
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("Drift detected", errs)
            self.assertIn("Forbidden token `axiom`", errs)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sync", action="store_true", help="Copy canonical LLVMAst/TargetIR files into bridge")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        res = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests)
        )
        return 0 if res.wasSuccessful() else 1

    rep = check_bridge_tree(ROOT_DIR, sync_mirrors=args.sync)
    if args.json:
        print(json.dumps(rep, indent=2, sort_keys=True))
    else:
        print(
            f"[lean-mlir-bridge-sync] ok={rep['ok']} "
            f"rev={rep['pinned_lean_mlir_rev'][:12]} "
            f"mirrors={len(rep.get('mirrored_files', {}))} "
            f"proof_files={rep.get('proof_files_checked', 0)}"
        )
    if not rep["ok"]:
        for err in rep["errors"]:  # type: ignore[union-attr]
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
