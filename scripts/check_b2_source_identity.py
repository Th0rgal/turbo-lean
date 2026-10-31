#!/usr/bin/env python3
"""Fail closed unless the proof package imports the exact compiler-side sources."""
import hashlib
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FILES = (
    "IR/Types.lean", "IR/AST.lean", "IR/Codec.lean",
    "Semantics/Value.lean", "Semantics/Eval.lean", "Backend/Clif.lean",
)
CLIFV_REV = "5018b9509dc124154dbe08a5bd85862595d8eab7"


def main():
    for name in FILES:
        compiler = ROOT / "lean/LeanNative" / name
        proof = ROOT / "research/b2-proofs/vendor/LeanNative" / name
        a, b = compiler.read_bytes(), proof.read_bytes()
        if a != b:
            raise SystemExit(f"B2 source drift: {name}")
        print(f"{hashlib.sha256(a).hexdigest()}  {name}")
    dep = ROOT / "research/clifv"
    rev = subprocess.check_output(["git", "-C", str(dep), "rev-parse", "HEAD"], text=True).strip()
    if rev != CLIFV_REV:
        raise SystemExit(f"B2 clifv revision drift: {rev}")
    if subprocess.check_output(["git", "-C", str(dep), "status", "--porcelain", "--untracked-files=no"], text=True):
        raise SystemExit("B2 clifv has modified tracked sources")
    print(f"clifv {rev} (clean)")


if __name__ == "__main__":
    main()
