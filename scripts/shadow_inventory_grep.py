#!/usr/bin/env python3
"""Independent (source-text) inventory of shadow-semantics target declarations.

Cross-check for scripts/check_shadow_semantics.lean (Track B0 deliverable 3): lists every
user-written declaration in a pinned target module or under a pinned namespace by scanning
`.lean` sources with regexes only (no Lean), then diffs against the checker's
`--coverage-out` TSV. Any declaration found here but absent from the checker's coverage is an
inventory gap and fails (exit 1). Names the checker covers but this scanner misses (generated
instances, structure projections, `deriving` output) are reported as informational only.

Usage: scripts/shadow_inventory_grep.py COVERAGE.tsv
"""
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN = REPO / "lean"
INV = json.loads((REPO / "scripts/shadow_inventory.json").read_text())

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:(\[{]+)"
)
NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)")
SEC_OPEN = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
MUTUAL = re.compile(r"^\s*mutual\b")
CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_'!?]*)\b")
FIELD = re.compile(r"^\s+([A-Za-z_][A-Za-z0-9_'!?]*)\s*:")


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(LEAN).with_suffix("").parts)


def strip_comments(text: str) -> str:
    # block comments (nesting-aware) and line comments
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return re.sub(r"--[^\n]*", "", "".join(out))


def scan(path: Path):
    """Yield (fully qualified name, line) for each declaration in `path`, plus the constructors
    of `inductive` types and the fields of `structure`s (they are user-written target-side
    declarations too)."""
    stack = []  # entries: ("ns", parts) | ("sec", None) | ("mutual", None)
    owner = None  # (kind, fully qualified type name) while inside an inductive / structure body
    for lineno, line in enumerate(strip_comments(path.read_text()).splitlines(), 1):
        if owner and line.strip() and not line[0].isspace() and not line.lstrip().startswith("|"):
            owner = None
        if owner:
            kind, tname = owner
            if kind in ("inductive",) and (m := CTOR.match(line)):
                yield f"{tname}.{m.group(1)}", lineno
                continue
            if kind in ("structure", "class") and (m := FIELD.match(line)) and m.group(1) != "deriving":
                yield f"{tname}.{m.group(1)}", lineno
                continue
        if m := NS_OPEN.match(line):
            stack.append(("ns", m.group(1).split(".")))
            continue
        if MUTUAL.match(line):
            stack.append(("mutual", None))
            continue
        if SEC_OPEN.match(line):
            stack.append(("sec", None))
            continue
        if m := END.match(line):
            if stack:
                stack.pop()
            continue
        if m := DECL.match(line):
            kind, name = m.groups()
            if kind == "instance" and (name.startswith(":") or name in ("where",)):
                continue  # anonymous instance: no user-visible name to compare
            name = name.lstrip("_root_.") if name.startswith("_root_.") else name
            prefix = [p for k, ps in stack if k == "ns" for p in ps]
            full = ".".join(prefix + [name]) if not m.group(2).startswith("_root_.") else name
            yield full, lineno
            if kind in ("inductive", "structure", "class"):
                owner = (kind, full)


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    covered = {}
    for row in Path(sys.argv[1]).read_text().splitlines():
        if row.strip():
            n, loc = row.split("\t")
            covered[n] = loc
    modules = set(INV["modules"])
    namespaces = INV["namespaces"]
    found = {}
    for root in INV["source_roots"]:
        root_file = LEAN / f"{root}.lean"
        paths = ([root_file] if root_file.is_file() else []) + sorted((LEAN / root).rglob("*.lean"))
        for path in paths:
            mod = module_of(path)
            for full, line in scan(path):
                in_ns = any(full == ns or full.startswith(ns + ".") for ns in namespaces)
                if mod in modules or in_ns:
                    found.setdefault(full, f"{path.relative_to(REPO)}:{line}")
    missing = sorted(n for n in found if n not in covered)
    extra = sorted(n for n in covered if n not in found)
    print(f"[inventory-grep] source scan: {len(found)} declarations; checker coverage: {len(covered)}")
    print(f"[inventory-grep] in both: {len(found) - len(missing)}")
    print(f"[inventory-grep] checker-only (generated / not matched by regex; informational): {len(extra)}")
    for n in extra:
        print(f"    + {n}\t{covered[n]}")
    if missing:
        print(f"[inventory-grep] FAIL: {len(missing)} source declarations NOT covered by the checker:")
        for n in missing:
            print(f"    - {n}\t{found[n]}")
        return 1
    print("[inventory-grep] PASS: every source-level target declaration is covered by the checker")
    return 0


if __name__ == "__main__":
    sys.exit(main())
