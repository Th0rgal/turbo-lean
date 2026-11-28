#!/usr/bin/env python3
"""H3.4 Step 1: measured `con-leche` construct census.

`roadmap/HORIZONS.md` says no `con-leche` declaration would lower today, but it
infers this from the README, because the sources are pinned and not vendored.
This script measures it. It reads the exact `con-leche` commit pinned by
`verification/con-leche-bridge/` (`501589f5...`, toolchain `v4.35.0`), counts
the declarations in the Lean sources, and classifies every computational
declaration against the H3 blocker categories:

  recursive_inductive  mentions a recursive (self/mutually referential) inductive
  reset_reuse          reset/reuse *candidate*: matches on a recursive inductive
                       and builds a value of one (the compiler's reset/reuse
                       insertion pattern; reset/reuse are IR constructs, so a
                       source census can only find candidates)
  big_nat              mentions `Nat`/`ℕ` (arbitrary-precision runtime object)
  array_hashmap        `Array`/`#[`/`ByteArray`/`HashMap`/`HashSet`/... containers
  string               `String`/`Substring`/`Char`/string literals/interpolation
  closure_pap          `fun`/`λ`/`·` lambdas or function-typed binders
                       (closures and partial application)
  io                   `IO`/`EIO`/`BaseIO`/`ST`/`Task`/`IO.Ref`/`Std.Async`
  external_init_call   qualified call into an `Init`/`Std`/`Lean` runtime
                       namespace not defined by `con-leche`, or a local
                       `@[extern]`/`@[implemented_by]`/unsafe runtime primitive

A declaration also inherits the blockers carried by every local type it
names (`via_type`): fields of structures/inductives and the bodies of type
aliases, closed under a least fixpoint. con-leche's own `Name` holds a `String`
and a `Nat`, and `Expr`/`Level` hold `Name`s, so most kernel code inherits
`string`, `big_nat` and `recursive_inductive` this way. Prop-valued inductive
families are erased at runtime and are neither recursive nor inherited; a type
is recursive only when it (or its `mutual` block) occurs in a constructor
*argument* position, not merely in an indexed result type. Each declaration
sees only the types defined in its own module's import closure.

The method is source-level and fully deterministic: comments and string bodies
are stripped with a Lean-aware lexer, declaration headers are matched at line
starts, and each declaration's text runs to the next header. No Lean build is
needed. Two scopes are reported: `exe_closure` (the import closure of `Main`,
i.e. the shipped `con-leche` binary) and `repo` (every `.lean` file at the
commit).

Usage:
  python3 scripts/h3_con_leche_census.py                 # fetch pin, write JSON
  python3 scripts/h3_con_leche_census.py --con-leche-dir DIR
  python3 scripts/h3_con_leche_census.py --check         # offline validation
  python3 scripts/h3_con_leche_census.py --check --con-leche-dir DIR  # + exact recompute
  python3 scripts/h3_con_leche_census.py --self-test
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent.parent
BRIDGE_DIR = ROOT_DIR / "verification" / "con-leche-bridge"
OUTPUT_PATH = ROOT_DIR / "benchmarks" / "h3_con_leche_census.json"

SCHEMA_VERSION = 1
CENSUS_METHOD = "source-lexical-v1"
PINNED_CON_LECHE_URL = "https://github.com/leanprover/con-leche.git"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
EXE_ROOT_MODULE = "Main"

CATEGORIES = (
    "recursive_inductive",
    "reset_reuse",
    "big_nat",
    "array_hashmap",
    "string",
    "closure_pap",
    "io",
    "external_init_call",
)

DECL_KINDS = (
    "def", "partial_def", "unsafe_def", "abbrev", "instance", "opaque",
    "theorem", "axiom", "inductive", "structure", "class", "class_inductive",
)
FUNCTION_KINDS = ("def", "partial_def", "unsafe_def", "abbrev", "instance", "opaque")
TYPE_KINDS = ("inductive", "structure", "class", "class_inductive")
PROOF_KINDS = ("theorem", "axiom")

# --------------------------------------------------------------------------
# Lexing
# --------------------------------------------------------------------------

_IDENT_CHAR = re.compile(r"[\w'!?·₀-₟Ͱ-Ͽἀ-῿]")


def strip_lean(text: str) -> tuple[str, int, int]:
    """Blank out comments and string/char literal bodies, keeping newlines.

    Returns (stripped_text, string_literal_count, interpolated_string_count).
    String literals become `""`; char literals become `' '`.
    """
    out: list[str] = []
    n = len(text)
    i = 0
    depth = 0
    strings = 0
    interps = 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == '"':
            strings += 1
            if text[max(0, i - 2):i] in ("s!", "m!", "f!"):
                interps += 1
            out.append('"')
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out.append("  " if text[i + 1] != "\n" else " \n")
                    i += 2
                    continue
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            out.append('"')
            i += 1
            continue
        if c == "'" and (i == 0 or not _IDENT_CHAR.match(text[i - 1])):
            m = re.compile(r"'(\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'").match(text, i)
            if m:
                out.append("' " + " " * (len(m.group(0)) - 3) + "'")
                i = m.end()
                continue
        out.append(c)
        i += 1
    return "".join(out), strings, interps


IDENT_RE = re.compile(r"(?<![\w'.])([A-Za-z_Ͱ-Ͽµℕ][\w'!?ℕ]*(?:\.[A-Za-z_Ͱ-Ͽ][\w'!?]*)*)")


def tokens(text: str) -> list[str]:
    return IDENT_RE.findall(text)


# --------------------------------------------------------------------------
# Declarations
# --------------------------------------------------------------------------

ATTR = r"(?:@\[[^\]]*\]\s*)*"
MODS = r"(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta)\s+)*"
HEADER_RE = re.compile(
    r"^[ \t]*(?P<attrs>" + ATTR + r")(?P<mods>" + MODS + r")"
    r"(?P<kw>class\s+inductive|theorem|lemma|def|abbrev|instance|opaque|axiom|inductive|structure|class)\b"
    r"(?P<rest>[^\n]*)",
    re.M,
)
NAME_RE = re.compile(r"\s*(?:\(priority\s*:=[^)]*\)\s*)?([^\s:({\[⦃]+)")
SCOPE_RE = re.compile(r"^[ \t]*(namespace|section|end|mutual)\b[ \t]*([^\s]*)", re.M)
DERIVING_RE = re.compile(r"\bderiving\s+(?!instance\b)([\w.]+(?:\s*,\s*[\w.]+)*)")
DERIVING_INSTANCE_RE = re.compile(r"^[ \t]*deriving\s+instance\s+([\w.]+(?:\s*,\s*[\w.]+)*)\s+for\s+([\w.]+(?:\s*,\s*[\w.]+)*)", re.M)
EXTERN_ATTR_RE = re.compile(r"@\[[^\]]*\b(extern|implemented_by|export)\b[^\]]*\]")


def decl_kind(kw: str, mods: str) -> str:
    kw = re.sub(r"\s+", " ", kw)
    if kw == "class inductive":
        return "class_inductive"
    if kw == "lemma":
        return "theorem"
    if kw == "def":
        if re.search(r"\bpartial\b", mods):
            return "partial_def"
        if re.search(r"\bunsafe\b", mods):
            return "unsafe_def"
    return kw


def parse_decls(stripped: str) -> list[dict]:
    """Split a stripped module into declarations with their full text."""
    scope_events = [(m.start(), m.group(1), m.group(2)) for m in SCOPE_RE.finditer(stripped)]
    headers = list(HEADER_RE.finditer(stripped))
    # Body boundaries: next header or next scope event, whichever is first.
    boundaries = sorted({m.start() for m in headers} | {p for p, _, _ in scope_events} | {len(stripped)})
    decls = []
    ns_stack: list[tuple[str, str]] = []
    mutual_id = None
    mutual_counter = 0
    ev_i = 0
    for m in headers:
        while ev_i < len(scope_events) and scope_events[ev_i][0] < m.start():
            _, kind, arg = scope_events[ev_i]
            if kind in ("namespace", "section"):
                ns_stack.append((kind, arg))
            elif kind == "mutual":
                mutual_counter += 1
                mutual_id = mutual_counter
                ns_stack.append(("mutual", ""))
            elif kind == "end" and ns_stack:
                k, _ = ns_stack.pop()
                if k == "mutual":
                    mutual_id = None
            ev_i += 1
        end = next(b for b in boundaries if b > m.start())
        body = stripped[m.start():end]
        kind = decl_kind(m.group("kw"), m.group("mods"))
        name = None
        rest = m.group("rest")
        if kind == "instance":
            nm = re.match(r"\s*(?:\(priority\s*:=[^)]*\)\s*)?([A-Za-z_][\w'.]*)\s*(?::|\(|\{|\[|⦃)", rest)
            # `instance foo : C` is named; `instance : C` is anonymous.
            if nm and not rest.lstrip().startswith(":"):
                name = nm.group(1)
        else:
            nm = NAME_RE.match(rest)
            if nm:
                name = nm.group(1)
        ns = ".".join(a for k, a in ns_stack if k == "namespace" and a)
        qual = None
        if name:
            qual = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
        decls.append({
            "kind": kind,
            "name": name,
            "qual": qual,
            "mods": m.group("mods"),
            "attrs": m.group("attrs"),
            "body": body,
            "mutual": mutual_id,
            "line": stripped.count("\n", 0, m.start()) + 1,
        })
    return decls


def signature(body: str) -> str:
    """Header up to the first top-level `:=`, `where` or `|` alternative."""
    m = re.search(r":=|\bwhere\b|\n[ \t]*\|", body)
    return body[: m.start()] if m else body


def result_is_sort(body: str) -> bool:
    sig = signature(body)
    return bool(re.search(r":\s*(?:Prop|Sort\b[^\n]*|Type\b[^\n]*)\s*$", sig.strip()))


TYPE_FORMERS = {"StateT", "ReaderT", "ExceptT", "OptionT", "StateRefT", "EStateM", "Except", "Option",
                "List", "Array", "IO", "EIO", "BaseIO", "ST", "EST", "Id", "Prod", "Sum", "Subtype", "Fin",
                "Std.HashMap", "Std.HashSet", "HashMap", "HashSet", "ByteArray", "Task", "Thunk", "Lean.HashMap"}


def is_type_valued(decl: dict) -> bool:
    """`def T : Type := …`, or an unannotated `abbrev M := StateT S IO`."""
    body = decl["body"]
    if result_is_sort(body):
        return True
    if decl["kind"] != "abbrev" or ":=" not in body:
        return False
    sig, rhs = body.split(":=", 1)
    if re.search(r"\)\s*:|^\s*abbrev\s+\S+\s*:", sig, re.M):
        return False  # has an explicit (non-sort) result type
    m = re.match(r"\s*([A-Z][\w.']*)", rhs)
    return bool(m and (m.group(1) in TYPE_FORMERS or m.group(1).split(".")[0] in TYPE_FORMERS))


def type_ctor_region(body: str, name: str) -> str:
    """Constructor/field text of an inductive/structure (no `with`/`deriving`)."""
    sig_end = re.search(r"\bwhere\b|\n[ \t]*\|", body)
    region = body[sig_end.start():] if sig_end else ""
    cut = re.search(r"^[ \t]*(?:with\b|deriving\b)", region, re.M)
    return region[: cut.start()] if cut else region


_OPEN, _CLOSE = "([{⦃⟨", ")]}⦄⟩"


def _top_level_split(text: str, sep: str) -> list[str]:
    parts, depth, cur, i = [], 0, [], 0
    while i < len(text):
        ch = text[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
        if depth == 0 and text.startswith(sep, i) and not (sep == "|" and text[i:i + 2] in ("||", "|>")):
            parts.append("".join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(ch)
        i += 1
    parts.append("".join(cur))
    return parts


def ctor_argument_text(body: str, kind: str) -> str:
    """Text of constructor *argument* positions only.

    For `| step (x : A) : B → T i j` the result type `T i j` is dropped, so an
    indexed family that merely names itself in its constructors' result types
    is not mistaken for a recursive type. Structure fields are kept whole.
    """
    region = type_ctor_region(body, "")
    if kind in ("structure", "class"):
        return region
    out = []
    for alt in _top_level_split(region, "|")[1:]:
        alt = re.sub(r"^\s*[A-Za-z_][\w']*", "", alt, count=1)
        depth, last = 0, -1
        for i, ch in enumerate(alt):
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth = max(0, depth - 1)
            elif ch == ":" and depth == 0 and alt[i + 1:i + 2] != "=":
                last = i
        binders, ret = (alt[:last], alt[last + 1:]) if last >= 0 else (alt, "")
        out.append(binders + " " + " ".join(_top_level_split(ret, "→")[:-1]))
    return "\n".join(out)


def is_prop_family(body: str) -> bool:
    """`inductive R : A → B → Prop` / `structure S : Prop`: erased at runtime."""
    sig = re.split(r"\bwhere\b|\n[ \t]*\|", body, maxsplit=1)[0]
    return bool(re.search(r"(?:^|:|→)\s*Prop\s*$", sig.strip()))


def ctor_names(body: str, kind: str) -> list[str]:
    if kind in ("structure", "class"):
        m = re.search(r"^[ \t]*(\w+)\s*::", body, re.M)
        return [m.group(1) if m else "mk"]
    return re.findall(r"^[ \t]*\|\s*([A-Za-z_][\w']*)", type_ctor_region(body, ""), re.M)


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------

CORE_RECURSIVE_TYPES = {"List"}  # recursive inductives from Init used as values
NAT_TOKENS = {"Nat", "ℕ"}
ARRAY_HEADS = {"Array": "array", "ByteArray": "byte_array", "FloatArray": "float_array",
               "Subarray": "array", "HashMap": "hash_map", "HashSet": "hash_set",
               "DHashMap": "hash_map", "PersistentHashMap": "hash_map", "PHashMap": "hash_map",
               "RBMap": "tree_map", "TreeMap": "tree_map", "RBTree": "tree_map", "TreeSet": "tree_map",
               "AssocList": "hash_map", "PersistentArray": "array", "Vector": "array"}
STRING_HEADS = {"String", "Substring", "Char"}
IO_HEADS = {"IO", "EIO", "BaseIO", "ST", "EST", "Task", "IO.Ref", "ST.Ref", "IO.FS", "IO.Process",
            "IO.Promise", "Std.Async", "Async", "Std.Channel", "Std.Mutex", "Mutex", "Channel",
            # Lean elaborator monads run in `IO` (`CoreM` = ReaderT/StateRefT over EIO).
            "CoreM", "MetaM", "TermElabM", "CommandElabM", "Elab.TermElabM", "Elab.Command",
            "Meta.MetaM", "Core.CoreM", "Lean.Elab", "Lean.Meta", "Lean.Core"}
INIT_NAMESPACES = {"Nat", "Int", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float", "Float32",
                   "Char", "String", "Substring", "Array", "ByteArray", "FloatArray", "Subarray",
                   "List", "Option", "Except", "IO", "EIO", "BaseIO", "ST", "Task", "Std", "Lean",
                   "Thread", "Id", "StateT", "ReaderT", "ExceptT", "StateRefT", "EStateM", "Bool",
                   "Fin", "BitVec", "Prod", "Sum", "Subtype", "Function", "Hashable", "System",
                   "Vector", "HashMap", "HashSet", "Thunk", "Ordering", "Decidable", "Ord"}
UNSAFE_PRIMITIVES = {"unsafeCast", "ptrAddrUnsafe", "withPtrAddr", "withPtrEq", "ptrEq", "isExclusiveUnsafe",
                     "unsafeBaseIO", "unsafeIO", "unsafeEIO", "panic!", "panic", "dbgTrace", "dbg_trace",
                     "unreachable!", "mixHash", "hash"}


def _heads(tok: str) -> tuple[str, str]:
    parts = tok.split(".")
    return parts[0], ".".join(parts[:2])


INHERITED = ("recursive_inductive", "big_nat", "array_hashmap", "string", "closure_pap", "io")
PATTERN_RE = re.compile(r"(?:^|\bfun)[ \t]*\|[^\n]*?=>", re.M)


def token_hits(text: str, toks: list[str], local_heads: set[str]) -> dict[str, set[str]]:
    """Blockers visible in the text itself (no type inheritance)."""
    hits: dict[str, set[str]] = {c: set() for c in CATEGORIES}
    for t in toks:
        h0, h1 = _heads(t)
        last = t.rsplit(".", 1)[-1]
        if t in NAT_TOKENS or h0 in NAT_TOKENS:
            hits["big_nat"].add("nat_type_or_op")
        if h0 in ARRAY_HEADS or (last in ARRAY_HEADS and h0 in ("Std", "Lean")):
            hits["array_hashmap"].add(ARRAY_HEADS[h0 if h0 in ARRAY_HEADS else last])
        if h0 in STRING_HEADS:
            hits["string"].add(h0.lower())
        if h0 in IO_HEADS or h1 in IO_HEADS:
            hits["io"].add(h1 if h1 in IO_HEADS else h0)
        if "." in t and h0 in INIT_NAMESPACES and h0 not in local_heads:
            hits["external_init_call"].add("qualified:" + h0)
        if t in UNSAFE_PRIMITIVES:
            hits["external_init_call"].add("primitive:" + t.rstrip("!"))
    if re.search(r"#\[", text):
        hits["array_hashmap"].add("array")
    return hits


def classify(decl: dict, ctx: dict) -> dict[str, list[str]]:
    """Return {category: [sub-tags]} for a computational declaration.

    Direct hits come from the declaration's own text. A local type named in
    the declaration contributes the blockers of its fields, transitively
    (sub-tag `via_type`), so `def f (e : Env) : Bool` is not blocker-free when
    `Env` holds `Name`s and `HashMap`s.
    """
    body = decl["body"]
    mod = decl["module"]
    toks = tokens(body)
    tokset = set(toks)
    comps = {c for t in toks for c in t.split(".")}
    hits = token_hits(body, toks, ctx["local_namespaces"])

    rec_types = ctx["recursive_types"][mod]
    rec_hit = sorted(t for t in rec_types if t in comps)
    if rec_hit:
        hits["recursive_inductive"].add("local" if any(t not in CORE_RECURSIVE_TYPES for t in rec_hit) else "core_list")
        has_match = bool(re.search(r"\bmatch\b|^[ \t]*\||\bfun[ \t]*\|", body, re.M))
        rhs = PATTERN_RE.sub(" ", body)
        builds = any(
            re.search(r"(?<![\w'])\." + re.escape(c) + r"\b", rhs) or re.search(re.escape(f"{t}.{c}") + r"\b", rhs)
            for t in rec_hit for c in rec_types[t][1]
        ) or ("::" in rhs and "List" in rec_hit) or ("⟨" in rhs and any(rec_types[t][0] in ("structure", "class") for t in rec_hit))
        if has_match and builds:
            hits["reset_reuse"].add("match_and_rebuild")
    if re.search(r"withExclusiveUnsafe|lean_is_exclusive_obj|isExclusiveUnsafe", body):
        hits["reset_reuse"].add("manual_exclusive")

    for t in sorted(comps & set(ctx["type_cats"][mod])):
        for c in ctx["type_cats"][mod][t]:
            hits[c].add("via_type")
    if '"' in body:
        hits["string"].add("string_literal")
    if re.search(r"\bfun\b|λ|·|<\$>|<\|>", body):
        hits["closure_pap"].add("lambda")
    if re.search(r"[(\[{⦃][^()\n]*:\s*[^()\n]*→", signature(body)):
        hits["closure_pap"].add("higher_order_binder")
    if EXTERN_ATTR_RE.search(decl["attrs"]):
        hits["external_init_call"].add("local_ffi_attr")
    return {c: sorted(v) for c, v in hits.items() if v}


# --------------------------------------------------------------------------
# Census
# --------------------------------------------------------------------------

def module_path(root: Path, mod: str) -> Path:
    return root / (mod.replace(".", "/").replace("«", "").replace("»", "") + ".lean")


IMPORT_RE = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»']+)", re.M)


def import_closure(root: Path, start: str) -> list[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = module_path(root, m)
        if not p.is_file():
            continue  # Init/Std/Lean: toolchain modules, not con-leche sources
        seen.add(m)
        stripped, _, _ = strip_lean(p.read_text(encoding="utf-8"))
        stack.extend(IMPORT_RE.findall(stripped))
    return sorted(seen)


def closure_files(root: Path, start: str) -> dict[str, Path]:
    """Import closure of `start`, keyed like `all_modules` (relative path)."""
    return {module_path(root, m).relative_to(root).with_suffix("").as_posix(): module_path(root, m)
            for m in import_closure(root, start)}


IMPORT_SRC_DIRS = ("", "tests/", "whitepaper/", "tests/olean/src/", "tests/e2e/src/")


def resolve_import(files: dict[str, Path], mod: str) -> str | None:
    rel = mod.replace("«", "").replace("»", "").replace(".", "/")
    for pre in IMPORT_SRC_DIRS:
        if pre + rel in files:
            return pre + rel
    return None


def all_modules(root: Path) -> dict[str, Path]:
    """Every `.lean` file at the commit, keyed by its relative path (module
    names are ambiguous for files such as `tests/olean/src/UpNum/12.34/5.lean`)."""
    mods = {}
    for p in sorted(root.rglob("*.lean")):
        rel = p.relative_to(root)
        if rel.parts[0] in (".git", ".lake"):
            continue
        mods[rel.with_suffix("").as_posix()] = p
    return dict(sorted(mods.items()))


def share(n: int, d: int) -> float:
    return round(n / d, 4) if d else 0.0


def census_scope(root: Path, files: dict[str, Path]) -> dict:
    modules = sorted(files)
    parsed = {}
    raw_bytes = {}
    lines = 0
    string_literals = 0
    for mod in modules:
        data = files[mod].read_bytes()
        raw_bytes[mod] = data
        text = data.decode("utf-8")
        lines += len(text.splitlines())
        stripped, nstr, _ = strip_lean(text)
        string_literals += nstr
        parsed[mod] = (stripped, parse_decls(stripped))

    manifest = hashlib.sha256()
    for mod in modules:
        manifest.update(f"{mod}\0{hashlib.sha256(raw_bytes[mod]).hexdigest()}\n".encode())

    # Type facts: recursive runtime inductives and their constructors, per
    # defining module. A declaration only sees the types of its own module's
    # import closure, so short names from unrelated test fixtures never leak.
    all_decls = [(mod, d) for mod in modules for d in parsed[mod][1]]
    types = [(mod, d) for mod, d in all_decls if d["kind"] in TYPE_KINDS and d["name"]]
    aliases = [(mod, d) for mod, d in all_decls
               if d["kind"] in FUNCTION_KINDS and d["kind"] != "instance" and d["name"]
               and is_type_valued(d) and not is_prop_family(d["body"])]
    groups: dict[tuple, set[str]] = {}
    for mod, d in types:
        if d["mutual"] is not None:
            groups.setdefault((mod, d["mutual"]), set()).add(d["name"].rsplit(".", 1)[-1])
    defined: dict[str, dict[str, tuple[str, tuple[str, ...]]]] = {m: {} for m in modules}
    local_type_heads = {d["name"].split(".")[0] for _, d in types} | {"ConLeche"}
    type_direct: dict[tuple[str, str], set[str]] = {}
    type_refs: dict[tuple[str, str], set[str]] = {}
    defined_all: dict[str, set[str]] = {m: set() for m in modules}
    recursive_names: list[str] = []
    type_stats = Counter()
    for mod, d in types:
        short = d["name"].rsplit(".", 1)[-1]
        group = groups.get((mod, d["mutual"]), {short}) if d["mutual"] is not None else {short}
        region = type_ctor_region(d["body"], short)
        rtoks = {t.rsplit(".", 1)[-1] for t in tokens(region)} | set(tokens(region))
        atoks = {t.rsplit(".", 1)[-1] for t in tokens(ctor_argument_text(d["body"], d["kind"]))}
        type_stats["types"] += 1
        key = (mod, short)
        defined_all[mod].add(short)
        if not is_prop_family(d["body"]):
            rtl = tokens(region)
            th = token_hits(region, rtl, local_type_heads)
            direct = {c for c in INHERITED if th[c]}
            if "→" in region:
                direct.add("closure_pap")
            if group & atoks:
                direct.add("recursive_inductive")
            type_direct[key] = type_direct.get(key, set()) | direct
            type_refs[key] = type_refs.get(key, set()) | {c for t in rtl for c in t.split(".")}
        if is_prop_family(d["body"]):
            type_stats["prop_valued"] += 1
        elif group & atoks:
            prev = defined[mod].get(short, (d["kind"], ()))
            defined[mod][short] = (d["kind"], tuple(sorted(set(prev[1]) | set(ctor_names(d["body"], d["kind"])))))
            recursive_names.append(d["qual"])
            type_stats["recursive"] += 1
        if rtoks & NAT_TOKENS:
            type_stats["with_nat_field"] += 1
        if rtoks & set(ARRAY_HEADS):
            type_stats["with_container_field"] += 1
        if rtoks & STRING_HEADS:
            type_stats["with_string_field"] += 1
        if "→" in region:
            type_stats["with_function_field"] += 1
    imports = {m: [r for r in (resolve_import(files, i) for i in IMPORT_RE.findall(parsed[m][0])) if r] for m in modules}
    visible_rec: dict[str, dict[str, tuple[str, tuple[str, ...]]]] = {}
    visible_types: dict[str, dict[str, tuple[str, str]]] = {}
    for mod in modules:
        seen, stack = set(), [mod]
        while stack:
            m = stack.pop()
            if m not in seen:
                seen.add(m)
                stack.extend(imports[m])
        vis = {t: ("inductive", ("cons", "nil")) for t in CORE_RECURSIVE_TYPES}
        vtypes: dict[str, tuple[str, str]] = {}
        for m in sorted(seen - {mod}) + [mod]:  # own module wins on a name clash
            vis.update(defined[m])
            vtypes.update({t: (m, t) for t in defined_all[m] if (m, t) in type_direct})
        visible_rec[mod] = vis
        visible_types[mod] = vtypes
    # Type aliases (`abbrev M := StateT S IO`): their bodies are their fields.
    for mod, d in aliases:
        short = d["name"].rsplit(".", 1)[-1]
        key = (mod, short)
        if key in type_direct:
            continue
        rhs = d["body"].split(":=", 1)[1] if ":=" in d["body"] else ""
        rtl = tokens(rhs)
        th = token_hits(rhs, rtl, local_type_heads)
        type_direct[key] = {c for c in INHERITED if th[c]}
        type_refs[key] = {c for t in rtl for c in t.split(".")}
        defined_all[mod].add(short)
    for mod in modules:
        seen, stack = set(), [mod]
        while stack:
            m = stack.pop()
            if m not in seen:
                seen.add(m)
                stack.extend(imports[m])
        for m in sorted(seen - {mod}) + [mod]:
            visible_types[mod].update({t: (m, t) for t in defined_all[m] if (m, t) in type_direct})
    # Transitive field blockers: least fixpoint over local runtime types.
    type_cats = {k: set(v) for k, v in type_direct.items()}
    changed = True
    while changed:
        changed = False
        for key in sorted(type_cats):
            vt = visible_types[key[0]]
            acc = set(type_cats[key])
            for r in type_refs[key] & set(vt):
                if vt[r] != key:
                    acc |= type_cats[vt[r]]
            if acc != type_cats[key]:
                type_cats[key] = acc
                changed = True
    ctx = {"recursive_types": visible_rec, "local_namespaces": local_type_heads,
           "type_cats": {m: {t: sorted(type_cats[k]) for t, k in vt.items()} for m, vt in visible_types.items()}}

    by_kind = Counter({k: 0 for k in DECL_KINDS})
    cat_counts = Counter({c: 0 for c in CATEGORIES})
    sub_counts: dict[str, Counter] = {c: Counter() for c in CATEGORIES}
    computational = 0
    noncomputable = 0
    sort_valued = 0
    blocker_free = 0
    anonymous_instances = 0
    combo = Counter()
    per_module_rows = []
    qual_names = []
    ffi_decls = []
    derived = 0
    for mod in modules:
        stripped, decls = parsed[mod]
        derived += sum(len(m.group(1).split(",")) for m in DERIVING_RE.finditer(stripped))
        derived += sum(len(m.group(1).split(",")) * len(m.group(2).split(","))
                       for m in DERIVING_INSTANCE_RE.finditer(stripped))
        mod_total = len(decls)
        mod_comp = 0
        mod_free = 0
        for d in decls:
            by_kind[d["kind"]] += 1
            if d["qual"]:
                qual_names.append(f"{mod}:{d['qual']}")
            elif d["kind"] == "instance":
                anonymous_instances += 1
            if d["kind"] not in FUNCTION_KINDS:
                continue
            if re.search(r"\bnoncomputable\b", d["mods"]):
                noncomputable += 1
                continue
            if is_type_valued(d):
                sort_valued += 1
                continue
            computational += 1
            mod_comp += 1
            if EXTERN_ATTR_RE.search(d["attrs"]):
                ffi_decls.append(f"{mod}:{d['qual'] or '<anonymous>'}")
            hits = classify(dict(d, module=mod), ctx)
            for c, subs in hits.items():
                cat_counts[c] += 1
                for s in subs:
                    sub_counts[c][s] += 1
            if not hits:
                blocker_free += 1
                mod_free += 1
            combo[len(hits)] += 1
        per_module_rows.append((mod, mod_total, mod_comp, mod_free))

    total = sum(by_kind.values())
    blockers = {}
    for c in CATEGORIES:
        blockers[c] = {
            "declarations": cat_counts[c],
            "share_of_computational": share(cat_counts[c], computational),
            "subcategories": {k: v for k, v in sorted(sub_counts[c].items(), key=lambda kv: (-kv[1], kv[0]))[:12]},
        }
    top = sorted(CATEGORIES, key=lambda c: (-cat_counts[c], c))
    return {
        "modules": len(modules),
        "source_lines": lines,
        "source_manifest_sha256": manifest.hexdigest(),
        "string_literals": string_literals,
        "declarations": {
            "total": total,
            "by_kind": {k: by_kind[k] for k in DECL_KINDS},
            "named": len(qual_names),
            "anonymous_instances": anonymous_instances,
            "qualified_names_sha256": hashlib.sha256("\n".join(sorted(qual_names)).encode()).hexdigest(),
            "function_like": sum(by_kind[k] for k in FUNCTION_KINDS),
            "proofs": sum(by_kind[k] for k in PROOF_KINDS),
            "types": sum(by_kind[k] for k in TYPE_KINDS),
            "computational": computational,
            "noncomputable": noncomputable,
            "sort_valued": sort_valued,
            "derived_instances": derived,
        },
        "types": {
            "total": type_stats["types"],
            "recursive": type_stats["recursive"],
            "prop_valued": type_stats["prop_valued"],
            "recursive_names": sorted(recursive_names),
            "with_nat_field": type_stats["with_nat_field"],
            "with_container_field": type_stats["with_container_field"],
            "with_string_field": type_stats["with_string_field"],
            "with_function_field": type_stats["with_function_field"],
        },
        "blockers": blockers,
        "top_blockers": top,
        "blocker_free_computational": blocker_free,
        "blocker_free_share": share(blocker_free, computational),
        "categories_per_declaration": {str(k): combo[k] for k in range(len(CATEGORIES) + 1)},
        "ffi_declarations": sorted(ffi_decls),
        "largest_modules": [
            {"module": m, "declarations": t, "computational": c, "blocker_free": f}
            for m, t, c, f in sorted(per_module_rows, key=lambda r: (-r[1], r[0]))[:10]
        ],
    }


def read_bridge_pin() -> tuple[str, str]:
    lakefile = (BRIDGE_DIR / "lakefile.toml").read_text(encoding="utf-8")
    m = re.search(r'name\s*=\s*"con-leche"[^\[]*?rev\s*=\s*"([0-9a-f]{40})"', lakefile, re.S)
    if not m:
        raise SystemExit("con-leche rev not found in verification/con-leche-bridge/lakefile.toml")
    toolchain = (BRIDGE_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()
    return m.group(1), toolchain


def git_head(path: Path) -> str:
    return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], check=True,
                          capture_output=True, text=True).stdout.strip()


def fetch_pinned(dest: Path) -> Path:
    for cmd in (["git", "init", "-q", str(dest)],
                ["git", "-C", str(dest), "fetch", "-q", "--depth", "1", PINNED_CON_LECHE_URL, PINNED_CON_LECHE_REV],
                ["git", "-C", str(dest), "-c", "advice.detachedHead=false", "checkout", "-q", "FETCH_HEAD"]):
        subprocess.run(cmd, check=True)
    return dest


def build_census(src: Path) -> dict:
    head = git_head(src)
    if head != PINNED_CON_LECHE_REV:
        raise SystemExit(f"con-leche checkout is at {head}, expected pinned {PINNED_CON_LECHE_REV}")
    toolchain = (src / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != PINNED_TOOLCHAIN:
        raise SystemExit(f"con-leche toolchain {toolchain!r} != {PINNED_TOOLCHAIN!r}")
    closure = closure_files(src, EXE_ROOT_MODULE)
    return {
        "schema_version": SCHEMA_VERSION,
        "horizon_step": "H3.4 step 1",
        "method": CENSUS_METHOD,
        "con_leche": {
            "url": PINNED_CON_LECHE_URL,
            "rev": PINNED_CON_LECHE_REV,
            "toolchain": PINNED_TOOLCHAIN,
            "pin_source": "verification/con-leche-bridge/lakefile.toml",
            "exe_root_module": EXE_ROOT_MODULE,
        },
        "categories": list(CATEGORIES),
        "notes": [
            "Source-level lexical census; no Lean elaboration. Counts are exact for the "
            "documented header grammar and blocker token rules in scripts/h3_con_leche_census.py.",
            "reset_reuse counts reset/reuse candidates (match on a recursive inductive plus "
            "rebuild of one) and manual exclusivity primitives; reset/reuse themselves are "
            "inserted by the compiler at IR level.",
            "external_init_call is a lower bound: dot-notation calls (x.size) are not resolved.",
            "Subcategory via_type: blocker inherited from a local type the declaration names "
            "(structure/inductive fields and type-alias bodies, transitively); other subcategories "
            "are direct textual occurrences. Subcategory counts overlap within a category.",
            "blocker_free_computational is the number of computational declarations with no "
            "category hit: the upper bound on what a first-order scalar-only lowering could take.",
            "computational = def/partial def/unsafe def/abbrev/instance/opaque that is not "
            "noncomputable and whose declared result is not Prop/Type/Sort.",
        ],
        "scopes": {
            "exe_closure": census_scope(src, closure),
            "repo": census_scope(src, all_modules(src)),
        },
    }


def canonical(data: dict) -> str:
    return json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


# --------------------------------------------------------------------------
# Schema check (offline)
# --------------------------------------------------------------------------

def _req(cond: bool, msg: str, errors: list[str]) -> None:
    if not cond:
        errors.append(msg)


def _is_int(v) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0


def validate(data: dict, raw: str | None = None) -> list[str]:
    errors: list[str] = []
    if not isinstance(data, dict):
        return ["top level is not an object"]
    expected_top = {"schema_version", "horizon_step", "method", "con_leche", "categories", "notes", "scopes"}
    _req(set(data) == expected_top, f"top-level keys {sorted(data)} != {sorted(expected_top)}", errors)
    _req(data.get("schema_version") == SCHEMA_VERSION, "schema_version mismatch", errors)
    _req(data.get("method") == CENSUS_METHOD, "method mismatch", errors)
    _req(data.get("categories") == list(CATEGORIES), "categories mismatch", errors)
    cl = data.get("con_leche", {})
    _req(cl.get("rev") == PINNED_CON_LECHE_REV, "con_leche.rev != script pin", errors)
    _req(cl.get("url") == PINNED_CON_LECHE_URL, "con_leche.url != script pin", errors)
    _req(cl.get("toolchain") == PINNED_TOOLCHAIN, "con_leche.toolchain != script pin", errors)
    try:
        rev, toolchain = read_bridge_pin()
        _req(rev == PINNED_CON_LECHE_REV, f"bridge lakefile pins {rev}, script pins {PINNED_CON_LECHE_REV}", errors)
        _req(toolchain == PINNED_TOOLCHAIN, f"bridge toolchain {toolchain} != {PINNED_TOOLCHAIN}", errors)
        manifest = json.loads((BRIDGE_DIR / "lake-manifest.json").read_text(encoding="utf-8"))
        revs = [p.get("rev") for p in manifest.get("packages", []) if p.get("name", "").strip("«»") == "con-leche"]
        _req(revs == [PINNED_CON_LECHE_REV], f"bridge lake-manifest con-leche revs {revs}", errors)
    except (OSError, SystemExit, ValueError) as e:
        errors.append(f"bridge pin unreadable: {e}")
    scopes = data.get("scopes", {})
    _req(isinstance(scopes, dict) and set(scopes) == {"exe_closure", "repo"}, "scopes must be exe_closure+repo", errors)
    for sname, s in (scopes.items() if isinstance(scopes, dict) else []):
        p = f"scopes.{sname}"
        for k in ("modules", "source_lines", "string_literals", "blocker_free_computational"):
            _req(_is_int(s.get(k)), f"{p}.{k} not a non-negative int", errors)
        _req(isinstance(s.get("source_manifest_sha256"), str) and re.fullmatch(r"[0-9a-f]{64}", s["source_manifest_sha256"] or "") is not None,
             f"{p}.source_manifest_sha256 malformed", errors)
        d = s.get("declarations", {})
        bk = d.get("by_kind", {})
        _req(list(bk) == list(DECL_KINDS) or set(bk) == set(DECL_KINDS), f"{p}.by_kind keys", errors)
        _req(all(_is_int(v) for v in bk.values()), f"{p}.by_kind values", errors)
        if errors:
            continue
        _req(d["total"] == sum(bk.values()), f"{p}.total != sum(by_kind)", errors)
        _req(d["function_like"] == sum(bk[k] for k in FUNCTION_KINDS), f"{p}.function_like", errors)
        _req(d["proofs"] == sum(bk[k] for k in PROOF_KINDS), f"{p}.proofs", errors)
        _req(d["types"] == sum(bk[k] for k in TYPE_KINDS), f"{p}.types", errors)
        _req(d["function_like"] == d["computational"] + d["noncomputable"] + d["sort_valued"],
             f"{p}: function_like != computational+noncomputable+sort_valued", errors)
        _req(d["named"] + d["anonymous_instances"] == d["total"], f"{p}: named+anonymous != total", errors)
        comp = d["computational"]
        b = s.get("blockers", {})
        _req(list(b) == list(CATEGORIES) or set(b) == set(CATEGORIES), f"{p}.blockers keys", errors)
        for c in CATEGORIES:
            e = b.get(c, {})
            _req(_is_int(e.get("declarations")) and e["declarations"] <= comp, f"{p}.{c}.declarations", errors)
            _req(e.get("share_of_computational") == share(e.get("declarations", 0), comp), f"{p}.{c}.share", errors)
            _req(isinstance(e.get("subcategories"), dict) and all(_is_int(v) and v <= e.get("declarations", 0)
                 for v in e["subcategories"].values()), f"{p}.{c}.subcategories", errors)
        _req(s.get("top_blockers") == sorted(CATEGORIES, key=lambda c: (-b[c]["declarations"], c)), f"{p}.top_blockers order", errors)
        cpd = s.get("categories_per_declaration", {})
        _req(set(cpd) == {str(i) for i in range(len(CATEGORIES) + 1)} and sum(cpd.values()) == comp,
             f"{p}.categories_per_declaration must partition computational", errors)
        _req(cpd.get("0") == s["blocker_free_computational"], f"{p}: blocker_free != categories_per_declaration[0]", errors)
        _req(sum(int(k) * v for k, v in cpd.items()) == sum(b[c]["declarations"] for c in CATEGORIES),
             f"{p}: category hits inconsistent", errors)
        _req(s.get("blocker_free_share") == share(s["blocker_free_computational"], comp), f"{p}.blocker_free_share", errors)
        t = s.get("types", {})
        _req(_is_int(t.get("total")) and t["total"] <= d["types"], f"{p}.types.total", errors)
        _req(t.get("recursive") == len(t.get("recursive_names", [])), f"{p}.types.recursive != len(names)", errors)
        _req(t.get("recursive_names") == sorted(t.get("recursive_names", [])), f"{p}.recursive_names unsorted", errors)
    if not errors and isinstance(scopes, dict):
        ec, rp = scopes["exe_closure"], scopes["repo"]
        _req(ec["modules"] <= rp["modules"] and ec["declarations"]["total"] <= rp["declarations"]["total"],
             "exe_closure must be a subset of repo", errors)
    if raw is not None and not errors:
        _req(raw == canonical(data), "committed JSON is not in canonical (sorted, indent=2) form", errors)
    return errors


# --------------------------------------------------------------------------
# Self-tests
# --------------------------------------------------------------------------

class CensusTests(unittest.TestCase):
    def test_strip_comments_strings(self):
        s, n, _ = strip_lean('def a := "inductive -- x" -- def b\n/- def c /- nested -/ -/ def d := \'"\'\n')
        self.assertEqual(n, 1)
        self.assertEqual([d["name"] for d in parse_decls(s)], ["a", "d"])

    def test_kinds_and_namespaces(self):
        src = ("namespace Foo\n@[inline] private partial def go : Nat := 1\ninstance : Inhabited Nat := ⟨0⟩\n"
               "theorem t : True := trivial\nend Foo\ndef P : Prop := True\n")
        ds = parse_decls(strip_lean(src)[0])
        self.assertEqual([(d["kind"], d["qual"]) for d in ds],
                         [("partial_def", "Foo.go"), ("instance", None), ("theorem", "Foo.t"), ("def", "P")])
        self.assertTrue(result_is_sort(ds[3]["body"]))
        self.assertFalse(result_is_sort(ds[0]["body"]))

    def test_recursive_and_reset_reuse(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "Main.lean").write_text(
                "import M\ndef main : IO Unit := IO.println s!\"hi\"\n", encoding="utf-8")
            (root / "M.lean").write_text(
                "inductive T where\n  | leaf\n  | node (l r : T)\n\ninductive E where\n  | a | b\n"
                "inductive R : T → T → Prop where\n  | refl (t : T) : R t t\n  | step : R a b → R b c → R a c\n"
                "inductive S : Type → Type where\n  | n : S Nat\n  | l : S T\n"
                "def T.swap : T → T\n  | .leaf => .leaf\n  | .node l r => .node r l\n"
                "def f (x : UInt64) : UInt64 := x + 1\n"
                "def g (xs : Array Nat) : Nat := xs.foldl (fun a b => a + b) 0\n"
                "structure Box where\n  ts : Array T\n"
                "def h (b : Box) : UInt8 := 0\n"
                "def isLeaf : T → Bool\n  | .leaf => true\n  | _ => false\n", encoding="utf-8")
            sc = census_scope(root, closure_files(root, "Main"))
            self.assertEqual(sc["modules"], 2)
            self.assertEqual(sc["types"]["recursive_names"], ["T"])
            b = sc["blockers"]
            self.assertEqual(b["reset_reuse"]["declarations"], 1)
            self.assertEqual(b["io"]["declarations"], 1)
            self.assertEqual(b["closure_pap"]["declarations"], 1)
            self.assertEqual(sc["blocker_free_computational"], 1)  # f only; h inherits via Box
            self.assertEqual(sc["declarations"]["computational"], 6)
            self.assertEqual(b["array_hashmap"]["declarations"], 2)
            self.assertEqual(b["array_hashmap"]["subcategories"].get("via_type"), 1)
            self.assertEqual(b["recursive_inductive"]["declarations"], 3)  # swap, h, isLeaf


# --------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--con-leche-dir", type=Path, help="existing checkout of the pinned con-leche commit")
    ap.add_argument("--check", action="store_true", help="validate the committed JSON (offline unless --con-leche-dir)")
    ap.add_argument("--output", type=Path, default=OUTPUT_PATH)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        r = unittest.TextTestRunner(verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(CensusTests))
        return 0 if r.wasSuccessful() else 1

    if args.check:
        try:
            raw = args.output.read_text(encoding="utf-8")
            data = json.loads(raw)
        except (OSError, ValueError) as e:
            print(f"FAIL: cannot read {args.output}: {e}", file=sys.stderr)
            return 1
        errors = validate(data, raw)
        if not errors and args.con_leche_dir:
            fresh = canonical(build_census(args.con_leche_dir.resolve()))
            if fresh != raw:
                errors.append("committed census differs from a fresh recompute at the pinned commit")
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        if errors:
            return 1
        ec = data["scopes"]["exe_closure"]
        print(f"OK: con-leche {PINNED_CON_LECHE_REV[:12]} exe_closure: {ec['declarations']['total']} declarations, "
              f"{ec['declarations']['computational']} computational, {ec['blocker_free_computational']} blocker-free")
        return 0

    rev, toolchain = read_bridge_pin()
    if (rev, toolchain) != (PINNED_CON_LECHE_REV, PINNED_TOOLCHAIN):
        print(f"FAIL: bridge pins {rev} / {toolchain}, script pins {PINNED_CON_LECHE_REV} / {PINNED_TOOLCHAIN}", file=sys.stderr)
        return 1
    if args.con_leche_dir:
        data = build_census(args.con_leche_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="con-leche-") as td:
            data = build_census(fetch_pinned(Path(td) / "con-leche"))
    text = canonical(data)
    errors = validate(json.loads(text), text)
    if errors:
        for e in errors:
            print(f"FAIL (generated): {e}", file=sys.stderr)
        return 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    print(f"wrote {args.output.relative_to(ROOT_DIR) if args.output.is_relative_to(ROOT_DIR) else args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
