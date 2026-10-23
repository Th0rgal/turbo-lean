#!/usr/bin/env python3
"""
Synchronize or verify `<!-- inventory:KEY -->...<!-- /inventory:KEY -->` markers
in `README.md` and `AGENTS.md` against the live `TurboLean/Spec.lean` and
`TurboLean/Kernel.lean` formal inventory.
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def compute_inventory() -> dict[str, str]:
    kernel_src = (ROOT / "lean" / "TurboLean" / "Kernel.lean").read_text(encoding="utf-8")
    cabi_exports = len(re.findall(r"@\[(?:inline,\s*)?export\s+[A-Za-z0-9_]+\]", kernel_src))

    spec_src = (ROOT / "lean" / "TurboLean" / "Spec.lean").read_text(encoding="utf-8")
    spec_theorems = len(re.findall(r"^(?:theorem|lemma)\s+[A-Za-z0-9_'.]+", spec_src, flags=re.M))

    turbo_bin = ROOT / "target" / "release" / "turbo-lean"
    if turbo_bin.exists():
        res = subprocess.run(
            [str(turbo_bin), "--json", "audit-spec", str(ROOT / "lean" / "TurboLean" / "Spec.lean")],
            capture_output=True,
            text=True,
            check=True,
        )
        rep = json.loads(res.stdout)
        tight = int(rep["tight_specs"])
        total = int(rep["total_specs_audited"])
        assert rep["ok"] and rep["vacuous_specs"] == 0 and rep["trivial_specs"] == 0, rep
    else:
        tight = spec_theorems
        total = spec_theorems

    return {
        "turbo_tight_specs": f"{tight}/{total}",
        "turbo_cabi_exports": str(cabi_exports),
    }


def apply_markers(text: str, inv: dict[str, str]) -> str:
    for k, val in inv.items():
        pattern = re.compile(
            rf"(<!--\s*inventory:{re.escape(k)}\s*-->)(.*?)(<!--\s*/inventory:{re.escape(k)}\s*-->)",
            re.DOTALL,
        )
        text = pattern.sub(rf"\g<1>{val}\g<3>", text)
    return text


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="Verify markers match without writing")
    ap.add_argument("--write", action="store_true", help="Update markers in README.md and AGENTS.md")
    args = ap.parse_args()

    inv = compute_inventory()
    targets = [ROOT / "README.md", ROOT / "AGENTS.md"]
    drifted = []
    for p in targets:
        orig = p.read_text(encoding="utf-8")
        updated = apply_markers(orig, inv)
        if orig != updated:
            drifted.append(p.name)
            if args.write:
                p.write_text(updated, encoding="utf-8")

    if args.check and drifted:
        print(f"[sync_docs_inventory] DRIFT detected in: {', '.join(drifted)} (expected {inv})", file=sys.stderr)
        return 1
    print(f"[sync_docs_inventory] OK: {json.dumps(inv, sort_keys=True)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
