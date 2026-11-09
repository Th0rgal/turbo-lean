#!/usr/bin/env python3
"""Upstream Pin, Rust Constant Sync & Zero-Nonstandard-Axiom Gate for `verification/con-leche-bridge/`.

Verifies:
1. `verification/con-leche-bridge/lean-toolchain` pins `leanprover/lean4:v4.35.0`, and both
   `lakefile.toml` and `lake-manifest.json` pin `leanprover/con-leche` at commit
   `501589f5680d9599dee1bcef30a420bc8924c490` with zero unexpected transitive packages.
2. `crates/turbo-lean/src/kernel.rs` pins the exact same `PINNED_CON_LECHE_REV` and
   `PINNED_CON_LECHE_TOOLCHAIN` constants so Rust binary invocation and Lean formal bridge
   pins cannot drift apart.
3. `ConLecheBridge` proof modules contain `#verify_con_leche_bridge_axioms` (>= 31 unique audited
   theorems via `Lean.collectAxioms` and `bridgedTheorems.Nodup`) and zero `sorry`, `sorryAx`,
   `admit`, `axiom`, `native_decide`, `bv_decide`, `trustCompiler`, or `ofReduceBool` tokens
   outside Lean comments/strings.
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
BRIDGE_DIR = ROOT_DIR / "verification" / "con-leche-bridge"

PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
PINNED_CON_LECHE_URL = "https://github.com/leanprover/con-leche.git"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"
KERNEL_RS_REL = "crates/turbo-lean/src/kernel.rs"
MIN_AUDITED_THEOREMS = 31

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


def check_bridge_tree(root_dir: Path) -> dict[str, object]:
    bridge_root = root_dir / "verification" / "con-leche-bridge"
    errors: list[str] = []

    if not bridge_root.is_dir():
        return {"ok": False, "errors": [f"Missing bridge directory: {bridge_root}"]}

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
        if PINNED_CON_LECHE_URL not in lf_txt:
            errors.append(f"lakefile.toml missing {PINNED_CON_LECHE_URL}")
        if PINNED_CON_LECHE_REV not in lf_txt:
            errors.append(f"lakefile.toml missing pinned rev {PINNED_CON_LECHE_REV}")

    manifest = bridge_root / "lake-manifest.json"
    if not manifest.is_file():
        errors.append(f"Missing committed {manifest}")
    else:
        try:
            mf = json.loads(manifest.read_text(encoding="utf-8"))
            if mf.get("name") not in ("«con-leche-bridge»", "con-leche-bridge"):
                errors.append(
                    f"lake-manifest.json root `name` must be '«con-leche-bridge»', got {mf.get('name')!r}"
                )
            raw_pkgs = mf.get("packages", [])
            if len(raw_pkgs) != 1:
                errors.append(
                    f"lake-manifest.json expected exactly 1 dependency (`con-leche`), got {len(raw_pkgs)}"
                )
            pkgs = {p.get("name"): p for p in raw_pkgs}
            cl_pkg = pkgs.get("«con-leche»") or pkgs.get("con-leche")
            if not cl_pkg or cl_pkg.get("rev") != PINNED_CON_LECHE_REV:
                errors.append(
                    f"lake-manifest.json con-leche rev mismatch: {cl_pkg.get('rev') if cl_pkg else None} != {PINNED_CON_LECHE_REV}"
                )
            if cl_pkg and cl_pkg.get("url") != PINNED_CON_LECHE_URL:
                errors.append(
                    f"lake-manifest.json con-leche url mismatch: {cl_pkg.get('url')} != {PINNED_CON_LECHE_URL}"
                )
        except Exception as exc:
            errors.append(f"Invalid lake-manifest.json: {exc}")

    kernel_rs = root_dir / KERNEL_RS_REL
    if not kernel_rs.is_file():
        errors.append(f"Missing {KERNEL_RS_REL}")
    else:
        ktxt = kernel_rs.read_text(encoding="utf-8")
        expected_rev_decl = f'pub const PINNED_CON_LECHE_REV: &str = "{PINNED_CON_LECHE_REV}";'
        expected_tc_decl = f'pub const PINNED_CON_LECHE_TOOLCHAIN: &str = "{PINNED_TOOLCHAIN}";'
        if expected_rev_decl not in ktxt:
            errors.append(f"{KERNEL_RS_REL} missing exact `{expected_rev_decl}`")
        if expected_tc_decl not in ktxt:
            errors.append(f"{KERNEL_RS_REL} missing exact `{expected_tc_decl}`")

    root_bridge_lean = bridge_root / "ConLecheBridge.lean"
    bridged_refs: list[str] = []
    if not root_bridge_lean.is_file():
        errors.append(f"Missing {root_bridge_lean}")
    else:
        rb_stripped = strip_lean_comments_and_strings(root_bridge_lean.read_text(encoding="utf-8"))
        if "#verify_con_leche_bridge_axioms" not in rb_stripped:
            errors.append("ConLecheBridge.lean missing `#verify_con_leche_bridge_axioms` gate")
        if "Lean.collectAxioms" not in rb_stripped:
            errors.append("ConLecheBridge.lean missing `Lean.collectAxioms` audit")
        if "theorem bridgedTheorems_nodup : bridgedTheorems.Nodup" not in rb_stripped:
            errors.append("ConLecheBridge.lean missing `theorem bridgedTheorems_nodup : bridgedTheorems.Nodup` uniqueness theorem")
        if f"def minAuditedTheorems : Nat := {MIN_AUDITED_THEOREMS}" not in rb_stripped:
            errors.append(
                f"ConLecheBridge.lean missing exact `def minAuditedTheorems : Nat := {MIN_AUDITED_THEOREMS}` floor"
            )
        bridged_refs = re.findall(r"``ConLecheBridge\.[A-Za-z0-9_?.']+", rb_stripped)
        if len(bridged_refs) != len(set(bridged_refs)):
            seen_refs: set[str] = set()
            dups = sorted({r for r in bridged_refs if r in seen_refs or seen_refs.add(r)})  # type: ignore[func-returns-value]
            errors.append(
                f"ConLecheBridge.lean contains duplicate bridged theorem references: {dups}"
            )
        if len(set(bridged_refs)) < MIN_AUDITED_THEOREMS:
            errors.append(
                f"ConLecheBridge.lean audits only {len(set(bridged_refs))} unique bridged theorems "
                f"(expected >= {MIN_AUDITED_THEOREMS})"
            )

    sub_lean_files = (
        sorted((bridge_root / "ConLecheBridge").rglob("*.lean"))
        if (bridge_root / "ConLecheBridge").is_dir()
        else []
    )
    proof_files = [root_bridge_lean, *sub_lean_files]
    if len(proof_files) < 2:
        errors.append("Expected ConLecheBridge.lean and ConLecheBridge/Soundness.lean")

    file_digests: dict[str, str] = {}
    for pf in proof_files:
        if not pf.is_file():
            errors.append(f"Missing proof file: {pf}")
            continue
        raw = pf.read_bytes()
        rel_str = str(pf.relative_to(root_dir))
        file_digests[rel_str] = sha256_bytes(raw)
        stripped = strip_lean_comments_and_strings(raw.decode("utf-8"))
        m = FORBIDDEN_PROOF_TOKENS.search(stripped)
        if m:
            errors.append(f"Forbidden token `{m.group(0).strip()}` in {rel_str}")

    return {
        "ok": len(errors) == 0,
        "pinned_toolchain": PINNED_TOOLCHAIN,
        "pinned_con_leche_rev": PINNED_CON_LECHE_REV,
        "bridged_theorems_count": len(set(bridged_refs)),
        "proof_files_checked": len(proof_files),
        "file_digests": file_digests,
        "errors": errors,
    }


class SelfTests(unittest.TestCase):
    def _copy_minimal_tree(self, root: Path) -> Path:
        kdst = root / KERNEL_RS_REL
        kdst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT_DIR / KERNEL_RS_REL, kdst)
        b_root = root / "verification" / "con-leche-bridge"
        (b_root / "ConLecheBridge").mkdir(parents=True, exist_ok=True)
        for fn in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "ConLecheBridge.lean"):
            shutil.copy2(BRIDGE_DIR / fn, b_root / fn)
        shutil.copy2(
            BRIDGE_DIR / "ConLecheBridge" / "Soundness.lean",
            b_root / "ConLecheBridge" / "Soundness.lean",
        )
        return b_root

    def test_live_repo_passes(self) -> None:
        rep = check_bridge_tree(ROOT_DIR)
        self.assertTrue(rep["ok"], rep)
        self.assertGreaterEqual(int(rep["bridged_theorems_count"]), MIN_AUDITED_THEOREMS)  # type: ignore[arg-type]

    def test_detects_pin_drift_and_forbidden_tokens(self) -> None:
        with tempfile.TemporaryDirectory(prefix="con-leche-sync-test-") as tmp:
            root = Path(tmp)
            b_root = self._copy_minimal_tree(root)
            drifted_mf = (BRIDGE_DIR / "lake-manifest.json").read_text(encoding="utf-8").replace(
                PINNED_CON_LECHE_REV, "0" * 40
            )
            (b_root / "lake-manifest.json").write_text(drifted_mf, encoding="utf-8")
            (b_root / "ConLecheBridge" / "Soundness.lean").write_text(
                'def ok := "-- sorry in string"\ntheorem bad : True := by sorry\n',
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("rev mismatch", errs)
            self.assertIn("Forbidden token `sorry`", errs)

    def test_detects_duplicate_and_undercounted_bridged_theorems(self) -> None:
        with tempfile.TemporaryDirectory(prefix="con-leche-sync-dup-") as tmp:
            root = Path(tmp)
            b_root = self._copy_minimal_tree(root)
            (b_root / "ConLecheBridge.lean").write_text(
                "def bridgedTheorems := [\n"
                "  ``ConLecheBridge.checkDecls_verified_model_exists,\n"
                "  ``ConLecheBridge.checkDecls_verified_model_exists\n"
                "]\n"
                "def minAuditedTheorems : Nat := 31\n"
                "theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by decide\n"
                "-- Lean.collectAxioms inside comment should not count\n"
                "def audit := Lean.collectAxioms\n"
                "#verify_con_leche_bridge_axioms\n",
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("duplicate bridged theorem references", errs)
            self.assertIn(f"expected >= {MIN_AUDITED_THEOREMS}", errs)

    def test_detects_missing_nodup_theorem(self) -> None:
        with tempfile.TemporaryDirectory(prefix="con-leche-sync-nodup-") as tmp:
            root = Path(tmp)
            b_root = self._copy_minimal_tree(root)
            orig = (b_root / "ConLecheBridge.lean").read_text(encoding="utf-8")
            (b_root / "ConLecheBridge.lean").write_text(
                orig.replace("bridgedTheorems.Nodup", "True").replace(
                    f"def minAuditedTheorems : Nat := {MIN_AUDITED_THEOREMS}",
                    "def minAuditedTheorems : Nat := 9",
                ),
                encoding="utf-8",
            )
            rep = check_bridge_tree(root)
            self.assertFalse(rep["ok"])
            errs = "\n".join(str(e) for e in rep["errors"])
            self.assertIn("bridgedTheorems.Nodup", errs)
            self.assertIn(f"def minAuditedTheorems : Nat := {MIN_AUDITED_THEOREMS}", errs)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        res = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests)
        )
        return 0 if res.wasSuccessful() else 1

    rep = check_bridge_tree(ROOT_DIR)
    if args.json:
        print(json.dumps(rep, indent=2, sort_keys=True))
    else:
        print(
            f"[con-leche-bridge-sync] ok={rep['ok']} "
            f"rev={str(rep['pinned_con_leche_rev'])[:12]} "
            f"theorems={rep.get('bridged_theorems_count', 0)} "
            f"proof_files={rep.get('proof_files_checked', 0)}"
        )
    if not rep["ok"]:
        for err in rep["errors"]:  # type: ignore[union-attr]
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
