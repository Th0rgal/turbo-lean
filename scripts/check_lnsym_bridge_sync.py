#!/usr/bin/env python3
"""Stage 3D: Exact Model Synchronization & Upstream Pin Gate for `verification/lnsym-bridge/`.

Verifies:
1. `verification/lnsym-bridge/LNSymBridge/MirroredModel.lean` contains byte-identical slices of:
   - `clmul64` and `clmul64Hi` from `lean/LeanNative/IR/Types.lean`
   - `namespace LNSym ... end LNSym` from `lean/LeanNative/Backend/Semantics.lean`
   preventing any drift or shadow divergence between the main `LeanNative` compiler and the
   upstream `leanprover/LNSym` formal bisimulation package.
2. `verification/lnsym-bridge/lean-toolchain` pins `leanprover/lean4:v4.35.0`, and both
   `lakefile.toml` and `lake-manifest.json` pin `leanprover/LNSym` at commit
   `49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c` (`ELFSage @ 5820b10ff6594100f736c4009278188e14e96535`,
   `doc-gen4 @ 0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae`).
3. `LNSymBridge` proof modules contain `#verify_lnsym_bridge_axioms` (>= 50 unique audited theorems
   via `Lean.collectAxioms` and `bridgedTheorems.Nodup`) and zero `sorry`, `sorryAx`, `admit`,
   `axiom`, `native_decide`, `bv_decide`, `trustCompiler`, or `ofReduceBool` tokens outside Lean
   comments/strings.
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
BRIDGE_DIR = ROOT_DIR / "verification" / "lnsym-bridge"

PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
PINNED_LNSYM_REV = "49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c"
PINNED_ELFSAGE_REV = "5820b10ff6594100f736c4009278188e14e96535"
PINNED_DOCGEN4_REV = "0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae"

TYPES_REL = "lean/LeanNative/IR/Types.lean"
SEMANTICS_REL = "lean/LeanNative/Backend/Semantics.lean"

PINNED_SLICE_DIGESTS: dict[str, str] = {
    TYPES_REL: "c12a593956b4f77b7ce8ba7e1d6fea66af7918df9aea989f6cf5dfb62bb13576",
    SEMANTICS_REL: "b0d3ee9c6f430389d3ec72cf544881f7bb9142fa74e50d9db96f35faae1cc516",
}

MIN_AUDITED_THEOREMS = 50

FORBIDDEN_PROOF_TOKENS = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|bv_decide|trustCompiler|ofReduceBool)\b",
    re.M,
)


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


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


def extract_canonical_types_slice(text: str) -> str:
    start_marker = "/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/\ndef clmul64"
    end_marker = "\n/-- Parity of the low 8 bits:"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate clmul64..clmul64Hi slice in {TYPES_REL}")
    return text[s_idx:e_idx]


def extract_canonical_lnsym_slice(text: str) -> str:
    start_marker = "namespace LNSym\n"
    end_marker = "\nend LNSym"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate `namespace LNSym ... end LNSym` slice in {SEMANTICS_REL}")
    return text[s_idx : e_idx + len(end_marker)]


def extract_mirrored_slice(text: str, rel: str) -> str:
    b_tag = f"-- BEGIN MIRRORED SLICE: {rel}\n"
    e_tag = f"\n-- END MIRRORED SLICE: {rel}"
    s_idx = text.find(b_tag)
    e_idx = text.find(e_tag, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Missing mirrored slice markers for {rel}")
    return text[s_idx + len(b_tag) : e_idx]


def render_mirrored_model(types_slice: str, lnsym_slice: str) -> str:
    return (
        "/-!\n"
        "# Stage 3D Mirrored `LeanNative` Carryless & `LNSym` Model\n\n"
        "This module contains exact, byte-synchronized slices of:\n"
        "1. `LeanNative.IR.clmul64` and `LeanNative.IR.clmul64Hi` (`lean/LeanNative/IR/Types.lean`)\n"
        "2. `LeanNative.Backend.Semantics.LNSym` (`lean/LeanNative/Backend/Semantics.lean`)\n\n"
        "Enforced byte-for-byte against the root `LeanNative` compiler by `scripts/check_lnsym_bridge_sync.py`.\n"
        "-/\n\n"
        "namespace LeanNative.IR\n\n"
        f"-- BEGIN MIRRORED SLICE: {TYPES_REL}\n"
        f"{types_slice}\n"
        f"-- END MIRRORED SLICE: {TYPES_REL}\n\n"
        "end LeanNative.IR\n\n"
        "namespace LeanNative.Backend.Semantics\n\n"
        f"-- BEGIN MIRRORED SLICE: {SEMANTICS_REL}\n"
        f"{lnsym_slice}\n"
        f"-- END MIRRORED SLICE: {SEMANTICS_REL}\n\n"
        "end LeanNative.Backend.Semantics\n"
    )


def check_bridge_tree(root_dir: Path, sync_mirrors: bool = False) -> dict[str, object]:
    bridge_root = root_dir / "verification" / "lnsym-bridge"
    errors: list[str] = []

    if not bridge_root.is_dir():
        return {"ok": False, "errors": [f"Missing bridge directory: {bridge_root}"]}

    types_path = root_dir / TYPES_REL
    sem_path = root_dir / SEMANTICS_REL
    mirrored_path = bridge_root / "LNSymBridge" / "MirroredModel.lean"
    slice_digests: dict[str, str] = {}

    if not types_path.is_file():
        errors.append(f"Missing canonical file: {types_path}")
    if not sem_path.is_file():
        errors.append(f"Missing canonical file: {sem_path}")

    if types_path.is_file() and sem_path.is_file():
        try:
            c_types = extract_canonical_types_slice(types_path.read_text(encoding="utf-8"))
            c_lnsym = extract_canonical_lnsym_slice(sem_path.read_text(encoding="utf-8"))
            slice_digests[TYPES_REL] = sha256_bytes(c_types.encode("utf-8"))
            slice_digests[SEMANTICS_REL] = sha256_bytes(c_lnsym.encode("utf-8"))
            for rel_key, expected_sha in PINNED_SLICE_DIGESTS.items():
                actual_sha = slice_digests.get(rel_key)
                if actual_sha != expected_sha:
                    errors.append(
                        f"Canonical slice SHA-256 mismatch for {rel_key}: "
                        f"{actual_sha} != {expected_sha}"
                    )
            if sync_mirrors:
                mirrored_path.parent.mkdir(parents=True, exist_ok=True)
                mirrored_path.write_text(render_mirrored_model(c_types, c_lnsym), encoding="utf-8")
            if not mirrored_path.is_file():
                errors.append(f"Missing mirrored model file: {mirrored_path}")
            else:
                m_txt = mirrored_path.read_text(encoding="utf-8")
                m_types = extract_mirrored_slice(m_txt, TYPES_REL)
                m_lnsym = extract_mirrored_slice(m_txt, SEMANTICS_REL)
                if m_types != c_types:
                    errors.append(
                        f"Drift detected in {TYPES_REL} slice "
                        "(run `python3 scripts/check_lnsym_bridge_sync.py --sync`)"
                    )
                if m_lnsym != c_lnsym:
                    errors.append(
                        f"Drift detected in {SEMANTICS_REL} slice "
                        "(run `python3 scripts/check_lnsym_bridge_sync.py --sync`)"
                    )
        except Exception as exc:
            errors.append(f"Slice extraction failed: {exc}")

    # Verify toolchain, lakefile.toml, and lake-manifest.json
    tc_file = bridge_root / "lean-toolchain"
    if not tc_file.is_file():
        errors.append(f"Missing {tc_file}")
    elif tc_file.read_text(encoding="utf-8").strip() != PINNED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain mismatch: {tc_file.read_text(encoding='utf-8').strip()!r} != {PINNED_TOOLCHAIN!r}"
        )

    lakefile = bridge_root / "lakefile.toml"
    if not lakefile.is_file():
        errors.append(f"Missing {lakefile}")
    else:
        lf_txt = lakefile.read_text(encoding="utf-8")
        if "https://github.com/leanprover/LNSym.git" not in lf_txt:
            errors.append("lakefile.toml missing https://github.com/leanprover/LNSym.git")
        if PINNED_LNSYM_REV not in lf_txt:
            errors.append(f"lakefile.toml missing pinned rev {PINNED_LNSYM_REV}")

    manifest = bridge_root / "lake-manifest.json"
    if not manifest.is_file():
        errors.append(f"Missing committed {manifest}")
    else:
        try:
            mf = json.loads(manifest.read_text(encoding="utf-8"))
            if mf.get("name") != "«lnsym-bridge»":
                errors.append(
                    f"lake-manifest.json root `name` must be '«lnsym-bridge»', got {mf.get('name')!r}"
                )
            pkgs = {p.get("name"): p for p in mf.get("packages", [])}
            lnsym_pkg = pkgs.get("lnsym")
            if not lnsym_pkg or lnsym_pkg.get("rev") != PINNED_LNSYM_REV:
                errors.append(
                    f"lake-manifest.json lnsym rev mismatch: {lnsym_pkg.get('rev') if lnsym_pkg else None} != {PINNED_LNSYM_REV}"
                )
            elf_pkg = pkgs.get("ELFSage")
            if not elf_pkg or elf_pkg.get("rev") != PINNED_ELFSAGE_REV:
                errors.append(
                    f"lake-manifest.json ELFSage rev mismatch: {elf_pkg.get('rev') if elf_pkg else None} != {PINNED_ELFSAGE_REV}"
                )
            dg_pkg = pkgs.get("«doc-gen4»") or pkgs.get("doc-gen4")
            if not dg_pkg or dg_pkg.get("rev") != PINNED_DOCGEN4_REV:
                errors.append(
                    f"lake-manifest.json doc-gen4 rev mismatch: {dg_pkg.get('rev') if dg_pkg else None} != {PINNED_DOCGEN4_REV}"
                )
        except Exception as exc:
            errors.append(f"Invalid lake-manifest.json: {exc}")

    # Scan proof files for forbidden tokens and axiom audit gate
    root_bridge_lean = bridge_root / "LNSymBridge.lean"
    bridged_refs: list[str] = []
    if not root_bridge_lean.is_file():
        errors.append(f"Missing {root_bridge_lean}")
    else:
        rb_stripped = strip_lean_comments_and_strings(root_bridge_lean.read_text(encoding="utf-8"))
        if "#verify_lnsym_bridge_axioms" not in rb_stripped:
            errors.append("LNSymBridge.lean missing `#verify_lnsym_bridge_axioms` gate")
        if "Lean.collectAxioms" not in rb_stripped:
            errors.append("LNSymBridge.lean missing `Lean.collectAxioms` audit")
        if "bridgedTheorems.Nodup" not in rb_stripped:
            errors.append("LNSymBridge.lean missing `bridgedTheorems.Nodup` uniqueness theorem")
        bridged_refs = re.findall(r"``LNSymBridge\.[A-Za-z0-9_?']+", rb_stripped)
        if len(bridged_refs) != len(set(bridged_refs)):
            seen_refs: set[str] = set()
            dups = sorted({r for r in bridged_refs if r in seen_refs or seen_refs.add(r)})  # type: ignore[func-returns-value]
            errors.append(
                f"LNSymBridge.lean contains duplicate bridged theorem references: {dups}"
            )
        if len(set(bridged_refs)) < MIN_AUDITED_THEOREMS:
            errors.append(
                f"LNSymBridge.lean audits only {len(set(bridged_refs))} unique bridged theorems "
                f"(expected >= {MIN_AUDITED_THEOREMS})"
            )
    proof_files = [
        root_bridge_lean,
        *sorted((bridge_root / "LNSymBridge").rglob("*.lean")),
    ]
    if len(proof_files) < 3:
        errors.append("Expected LNSymBridge.lean, MirroredModel.lean, and Bisimulation.lean")
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
        "pinned_lnsym_rev": PINNED_LNSYM_REV,
        "bridged_theorems_count": len(bridged_refs),
        "slice_digests": slice_digests,
        "proof_files_checked": len(proof_files),
        "errors": errors,
    }


class SelfTests(unittest.TestCase):
    def test_live_repo_passes(self) -> None:
        rep = check_bridge_tree(ROOT_DIR)
        self.assertTrue(rep["ok"], rep)
        self.assertGreaterEqual(rep["bridged_theorems_count"], MIN_AUDITED_THEOREMS)  # type: ignore[arg-type]

    def test_detects_slice_drift_and_bv_decide(self) -> None:
        with tempfile.TemporaryDirectory(prefix="lnsym-sync-test-") as tmp:
            root = Path(tmp)
            for rel in (TYPES_REL, SEMANTICS_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "lnsym-bridge"
            (b_root / "LNSymBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "LNSymBridge.lean"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            drifted = (BRIDGE_DIR / "LNSymBridge" / "MirroredModel.lean").read_text(encoding="utf-8")
            drifted = drifted.replace("def zero : QReg := ⟨0, 0⟩", "def zero : QReg := ⟨1, 0⟩")
            (b_root / "LNSymBridge" / "MirroredModel.lean").write_text(drifted, encoding="utf-8")
            (b_root / "LNSymBridge" / "Bisimulation.lean").write_text(
                'def ok := "-- bv_decide in string"\ntheorem bad (x : BitVec 8) : x = x := by bv_decide\n',
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])  # type: ignore[union-attr]
            self.assertIn("Drift detected", errs)
            self.assertIn("Forbidden token `bv_decide`", errs)

    def test_rejects_duplicate_and_undercounted_bridged_theorems(self) -> None:
        with tempfile.TemporaryDirectory(prefix="lnsym-thm-ratchet-") as tmp:
            root = Path(tmp)
            for rel in (TYPES_REL, SEMANTICS_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "lnsym-bridge"
            (b_root / "LNSymBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            for fn in ("MirroredModel.lean", "Bisimulation.lean"):
                shutil.copy2(BRIDGE_DIR / "LNSymBridge" / fn, b_root / "LNSymBridge" / fn)

            orig_root_lean = (BRIDGE_DIR / "LNSymBridge.lean").read_text(encoding="utf-8")
            dup_root_lean = orig_root_lean.replace(
                "``LNSymBridge.gf128_butterfly_program_run_28_field_spec",
                "``LNSymBridge.bv128ToQReg_qregToBv128",
                1,
            )
            (b_root / "LNSymBridge.lean").write_text(dup_root_lean, encoding="utf-8")
            rep_dup = check_bridge_tree(root)
            self.assertFalse(rep_dup["ok"])
            errs_dup = "\n".join(str(e) for e in rep_dup["errors"])  # type: ignore[union-attr]
            self.assertIn("duplicate bridged theorem references", errs_dup)

            short_root_lean = (
                "import LNSymBridge.Bisimulation\nimport Lean\n"
                "def bridgedTheorems := [``LNSymBridge.bv128ToQReg_qregToBv128]\n"
                "theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by decide\n"
                "def chk := Lean.collectAxioms\n"
                "#verify_lnsym_bridge_axioms\n"
            )
            (b_root / "LNSymBridge.lean").write_text(short_root_lean, encoding="utf-8")
            rep_short = check_bridge_tree(root)
            self.assertFalse(rep_short["ok"])
            errs_short = "\n".join(str(e) for e in rep_short["errors"])  # type: ignore[union-attr]
            self.assertIn(f"expected >= {MIN_AUDITED_THEOREMS}", errs_short)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sync", action="store_true", help="Re-render MirroredModel.lean from canonical slices")
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
            f"[lnsym-bridge-sync] ok={rep['ok']} "
            f"rev={str(rep['pinned_lnsym_rev'])[:12]} "
            f"theorems={rep.get('bridged_theorems_count', 0)} "
            f"slices={len(rep.get('slice_digests', {}))} "
            f"proof_files={rep.get('proof_files_checked', 0)}"
        )
    if not rep["ok"]:
        for err in rep["errors"]:  # type: ignore[union-attr]
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
