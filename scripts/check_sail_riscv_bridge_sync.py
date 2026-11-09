#!/usr/bin/env python3
"""Stage 3E / Milestone M5: Exact Model Synchronization & Upstream Pin Gate for `verification/sail-riscv-bridge/`.

Verifies:
1. `verification/sail-riscv-bridge/SailRiscvBridge/MirroredModel.lean` contains byte-identical slices of:
   - `riscvDivU64Spec` and `riscvRemU64Spec` from `lean/TurboLean/PolicyGates.lean`
   - `clmul64` and `clmul64Hi` from `lean/LeanNative/IR/Types.lean`
   preventing any drift or shadow divergence between the main `TurboLean` / `LeanNative` modules
   and the upstream `opencompl/sail-riscv-lean` formal RV64 bisimulation package.
2. `verification/sail-riscv-bridge/lean-toolchain` pins `leanprover/lean4:v4.29.0`, and both
   `lakefile.toml` and `lake-manifest.json` pin `opencompl/sail-riscv-lean` (`Lean_RV64D`) at commit
   `51c635c460125ac87955d061fcd902ce03b8011f` and `rems-project/lean-sail` (`Sail`) at commit
   `079463134b9c50450b8393e1566a09fc492a34d9` (`len(packages) == 2`).
3. `SailRiscvBridge` proof modules never import heavy monolithic generated modules
   (`LeanRV64D.InstsEnd`, `LeanRV64D.Step`, `LeanRV64D.ZicsrInsts`, or root `import LeanRV64D`),
   contain `#verify_sail_riscv_bridge_axioms` (>= 10 audited theorems via `Lean.collectAxioms`),
   and contain zero `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `bv_decide`,
   `trustCompiler`, or `ofReduceBool` tokens outside Lean comments/strings.
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
BRIDGE_DIR = ROOT_DIR / "verification" / "sail-riscv-bridge"

PINNED_TOOLCHAIN = "leanprover/lean4:v4.29.0"
PINNED_SAIL_RISCV_URL = "https://github.com/opencompl/sail-riscv-lean.git"
PINNED_SAIL_RISCV_REV = "51c635c460125ac87955d061fcd902ce03b8011f"
PINNED_SAIL_URL = "https://github.com/rems-project/lean-sail"
PINNED_SAIL_REV = "079463134b9c50450b8393e1566a09fc492a34d9"

POLICY_GATES_REL = "lean/TurboLean/PolicyGates.lean"
TYPES_REL = "lean/LeanNative/IR/Types.lean"

FORBIDDEN_PROOF_TOKENS = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|bv_decide|trustCompiler|ofReduceBool)\b",
    re.M,
)
FORBIDDEN_IMPORTS = re.compile(
    r"^\s*import\s+(?:LeanRV64D\s*$|LeanRV64D\.(?:InstsEnd|Step|ZicsrInsts)\b)",
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


def extract_canonical_policy_slice(text: str) -> str:
    start_marker = "@[inline]\ndef riscvDivU64Spec"
    end_marker = "\n\n@[inline]\ndef specAuditWitnessGate"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate riscvDivU64Spec..riscvRemU64Spec slice in {POLICY_GATES_REL}")
    return text[s_idx:e_idx]


def extract_canonical_types_slice(text: str) -> str:
    start_marker = "/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/\ndef clmul64"
    end_marker = "\n/-- Parity of the low 8 bits:"
    s_idx = text.find(start_marker)
    e_idx = text.find(end_marker, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Could not locate clmul64..clmul64Hi slice in {TYPES_REL}")
    return text[s_idx:e_idx]


def extract_mirrored_slice(text: str, rel: str) -> str:
    b_tag = f"-- BEGIN MIRRORED SLICE: {rel}\n"
    e_tag = f"\n-- END MIRRORED SLICE: {rel}"
    s_idx = text.find(b_tag)
    e_idx = text.find(e_tag, s_idx if s_idx >= 0 else 0)
    if s_idx < 0 or e_idx < 0:
        raise ValueError(f"Missing mirrored slice markers for {rel}")
    return text[s_idx + len(b_tag) : e_idx]


def render_mirrored_model(policy_slice: str, types_slice: str) -> str:
    return (
        "/-!\n"
        "# Stage 3E / Milestone `M5` Mirrored `TurboLean` & `LeanNative` RV64 Scalar/Zbc Model\n\n"
        "This module contains exact, byte-synchronized slices of:\n"
        "1. `TurboLean.PolicyGates.riscvDivU64Spec` and `TurboLean.PolicyGates.riscvRemU64Spec`\n"
        f"   (`{POLICY_GATES_REL}`)\n"
        "2. `LeanNative.IR.clmul64` and `LeanNative.IR.clmul64Hi`\n"
        f"   (`{TYPES_REL}`)\n\n"
        "Enforced byte-for-byte against the root `turbo-lean` repository by\n"
        "`scripts/check_sail_riscv_bridge_sync.py`.\n"
        "-/\n\n"
        "namespace TurboLean.PolicyGates\n\n"
        f"-- BEGIN MIRRORED SLICE: {POLICY_GATES_REL}\n"
        f"{policy_slice}\n"
        f"-- END MIRRORED SLICE: {POLICY_GATES_REL}\n\n"
        "end TurboLean.PolicyGates\n\n"
        "namespace LeanNative.IR\n\n"
        f"-- BEGIN MIRRORED SLICE: {TYPES_REL}\n"
        f"{types_slice}\n"
        f"-- END MIRRORED SLICE: {TYPES_REL}\n\n"
        "end LeanNative.IR\n"
    )


def check_bridge_tree(root_dir: Path, sync_mirrors: bool = False) -> dict[str, object]:
    bridge_root = root_dir / "verification" / "sail-riscv-bridge"
    errors: list[str] = []

    if not bridge_root.is_dir():
        return {"ok": False, "errors": [f"Missing bridge directory: {bridge_root}"]}

    policy_path = root_dir / POLICY_GATES_REL
    types_path = root_dir / TYPES_REL
    mirrored_path = bridge_root / "SailRiscvBridge" / "MirroredModel.lean"
    slice_digests: dict[str, str] = {}

    if not policy_path.is_file():
        errors.append(f"Missing canonical file: {policy_path}")
    if not types_path.is_file():
        errors.append(f"Missing canonical file: {types_path}")

    if policy_path.is_file() and types_path.is_file():
        try:
            c_policy = extract_canonical_policy_slice(policy_path.read_text(encoding="utf-8"))
            c_types = extract_canonical_types_slice(types_path.read_text(encoding="utf-8"))
            slice_digests[POLICY_GATES_REL] = sha256_bytes(c_policy.encode("utf-8"))
            slice_digests[TYPES_REL] = sha256_bytes(c_types.encode("utf-8"))
            if sync_mirrors:
                mirrored_path.parent.mkdir(parents=True, exist_ok=True)
                mirrored_path.write_text(render_mirrored_model(c_policy, c_types), encoding="utf-8")
            if not mirrored_path.is_file():
                errors.append(f"Missing mirrored model file: {mirrored_path}")
            else:
                m_txt = mirrored_path.read_text(encoding="utf-8")
                m_policy = extract_mirrored_slice(m_txt, POLICY_GATES_REL)
                m_types = extract_mirrored_slice(m_txt, TYPES_REL)
                if m_policy != c_policy:
                    errors.append(
                        f"Drift detected in {POLICY_GATES_REL} slice "
                        "(run `python3 scripts/check_sail_riscv_bridge_sync.py --sync`)"
                    )
                if m_types != c_types:
                    errors.append(
                        f"Drift detected in {TYPES_REL} slice "
                        "(run `python3 scripts/check_sail_riscv_bridge_sync.py --sync`)"
                    )
        except Exception as exc:
            errors.append(f"Slice extraction failed: {exc}")

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
        if PINNED_SAIL_RISCV_URL not in lf_txt:
            errors.append(f"lakefile.toml missing {PINNED_SAIL_RISCV_URL}")
        if PINNED_SAIL_RISCV_REV not in lf_txt:
            errors.append(f"lakefile.toml missing pinned rev {PINNED_SAIL_RISCV_REV}")

    manifest = bridge_root / "lake-manifest.json"
    if not manifest.is_file():
        errors.append(f"Missing committed {manifest}")
    else:
        try:
            mf = json.loads(manifest.read_text(encoding="utf-8"))
            if mf.get("name") not in ("«sail-riscv-bridge»", "sail-riscv-bridge"):
                errors.append(
                    f"lake-manifest.json root `name` must be '«sail-riscv-bridge»', got {mf.get('name')!r}"
                )
            raw_pkgs = mf.get("packages", [])
            if len(raw_pkgs) != 2:
                errors.append(
                    f"lake-manifest.json expected exactly 2 dependencies (`Lean_RV64D` and `Sail`), got {len(raw_pkgs)}"
                )
            pkgs = {p.get("name"): p for p in raw_pkgs}
            rv_pkg = pkgs.get("Lean_RV64D")
            if not rv_pkg or rv_pkg.get("rev") != PINNED_SAIL_RISCV_REV:
                errors.append(
                    f"lake-manifest.json Lean_RV64D rev mismatch: {rv_pkg.get('rev') if rv_pkg else None} != {PINNED_SAIL_RISCV_REV}"
                )
            if rv_pkg and rv_pkg.get("url") != PINNED_SAIL_RISCV_URL:
                errors.append(
                    f"lake-manifest.json Lean_RV64D url mismatch: {rv_pkg.get('url')} != {PINNED_SAIL_RISCV_URL}"
                )
            sail_pkg = pkgs.get("Sail")
            if not sail_pkg or sail_pkg.get("rev") != PINNED_SAIL_REV:
                errors.append(
                    f"lake-manifest.json Sail rev mismatch: {sail_pkg.get('rev') if sail_pkg else None} != {PINNED_SAIL_REV}"
                )
            if sail_pkg and not str(sail_pkg.get("url", "")).rstrip(".git").endswith("rems-project/lean-sail"):
                errors.append(
                    f"lake-manifest.json Sail url mismatch: {sail_pkg.get('url')} != {PINNED_SAIL_URL}"
                )
        except Exception as exc:
            errors.append(f"Invalid lake-manifest.json: {exc}")

    root_bridge_lean = bridge_root / "SailRiscvBridge.lean"
    bridged_refs: list[str] = []
    if not root_bridge_lean.is_file():
        errors.append(f"Missing {root_bridge_lean}")
    else:
        rb_stripped = strip_lean_comments_and_strings(root_bridge_lean.read_text(encoding="utf-8"))
        if "#verify_sail_riscv_bridge_axioms" not in rb_stripped:
            errors.append("SailRiscvBridge.lean missing `#verify_sail_riscv_bridge_axioms` gate")
        if "Lean.collectAxioms" not in rb_stripped:
            errors.append("SailRiscvBridge.lean missing `Lean.collectAxioms` audit")
        bridged_refs = re.findall(r"``SailRiscvBridge\.[A-Za-z0-9_?']+", rb_stripped)
        if len(bridged_refs) < 10:
            errors.append(
                f"SailRiscvBridge.lean audits only {len(bridged_refs)} bridged theorems (expected >= 10)"
            )

    sub_lean_files = (
        sorted((bridge_root / "SailRiscvBridge").rglob("*.lean"))
        if (bridge_root / "SailRiscvBridge").is_dir()
        else []
    )
    proof_files = [root_bridge_lean, *sub_lean_files]
    if len(proof_files) < 3:
        errors.append("Expected SailRiscvBridge.lean, MirroredModel.lean, and Bisimulation.lean")

    for pf in proof_files:
        if not pf.is_file():
            errors.append(f"Missing proof file: {pf}")
            continue
        rel_str = str(pf.relative_to(root_dir))
        stripped = strip_lean_comments_and_strings(pf.read_text(encoding="utf-8"))
        m = FORBIDDEN_PROOF_TOKENS.search(stripped)
        if m:
            errors.append(f"Forbidden token `{m.group(0).strip()}` in {rel_str}")
        mi = FORBIDDEN_IMPORTS.search(stripped)
        if mi:
            errors.append(f"Forbidden heavy import `{mi.group(0).strip()}` in {rel_str}")

    return {
        "ok": len(errors) == 0,
        "pinned_toolchain": PINNED_TOOLCHAIN,
        "pinned_sail_riscv_rev": PINNED_SAIL_RISCV_REV,
        "pinned_sail_rev": PINNED_SAIL_REV,
        "bridged_theorems_count": len(bridged_refs),
        "slice_digests": slice_digests,
        "proof_files_checked": len(proof_files),
        "errors": errors,
    }


class SelfTests(unittest.TestCase):
    def test_live_repo_passes(self) -> None:
        rep = check_bridge_tree(ROOT_DIR)
        self.assertTrue(rep["ok"], rep)

    def test_detects_slice_drift_forbidden_tokens_and_heavy_imports(self) -> None:
        with tempfile.TemporaryDirectory(prefix="sail-riscv-sync-test-") as tmp:
            root = Path(tmp)
            for rel in (POLICY_GATES_REL, TYPES_REL):
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            b_root = root / "verification" / "sail-riscv-bridge"
            (b_root / "SailRiscvBridge").mkdir(parents=True, exist_ok=True)
            for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "SailRiscvBridge.lean"):
                shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
            drifted = (BRIDGE_DIR / "SailRiscvBridge" / "MirroredModel.lean").read_text(encoding="utf-8")
            drifted = drifted.replace("0xffffffffffffffff", "0")
            (b_root / "SailRiscvBridge" / "MirroredModel.lean").write_text(drifted, encoding="utf-8")
            (b_root / "SailRiscvBridge" / "Bisimulation.lean").write_text(
                "import LeanRV64D.InstsEnd\n"
                'def ok := "-- bv_decide in string"\n'
                "theorem bad (x : BitVec 8) : x = x := by bv_decide\n",
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("Drift detected", errs)
            self.assertIn("Forbidden token `bv_decide`", errs)
            self.assertIn("Forbidden heavy import", errs)


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
            f"[sail-riscv-bridge-sync] ok={rep['ok']} "
            f"rev={str(rep['pinned_sail_riscv_rev'])[:12]} "
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
